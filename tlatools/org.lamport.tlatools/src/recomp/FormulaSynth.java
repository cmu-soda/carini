package recomp;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;
import java.util.stream.Collectors;

import tlc2.TLC;
import tlc2.Utils;

public class FormulaSynth {
	public static final String maxNumWorkersEnvVar = "FSYNTH_MAX_NUM_WORKERS";
	private static final String TMP_DIR = System.getProperty("java.io.tmpdir");
	private static final int MAX_NUM_THREADS = System.getenv(maxNumWorkersEnvVar) != null ? Integer.parseInt(System.getenv(maxNumWorkersEnvVar)) : 25;
	private static final int MAX_NUM_WORKERS = 15;
	private static final long SHUTDOWN_MULTIPLIER = 5L;
	
	private Map<Map<String,String>, Utils.Pair<Formula,AlloyTrace>> synthesizedFormulas;
	private List<FormulaSynthWorker> workers;
	private ExecutorService threadPool;
	private Random seed;
	private boolean synthComplete;

	private final Lock lock = new ReentrantLock();
	private final Condition aWorkerIsDone = lock.newCondition();
	
	public FormulaSynth(Random rseed) {
		resetMemberVars();
		this.seed = rseed;
	}
	
	/**
	 * Manually synchronized
	 * @param formula
	 */
	public void setFormula(final Formula formula, final Map<String,String> envVarType) {
		try {
			this.lock.lock();
			// only modify <synthesizedFormulas> if it's before the shutdown time
			if (!this.synthComplete) {
				this.synthesizedFormulas.put(envVarType, new Utils.Pair<>(formula,null));
			}
		}
		finally {
			lock.unlock();
		}
	}
	
	/**
	 * Manually synchronized
	 * @param trace
	 * @param workerId
	 * @param envVarType
	 */
	public void setTrace(final AlloyTrace trace, final Map<String,String> envVarType) {
		try {
			this.lock.lock();
			// only modify <synthesizedFormulas> if it's before the shutdown time
			if (!this.synthComplete) {
				Utils.assertTrue(this.synthesizedFormulas.containsKey(envVarType), "Missing key for: " + envVarType);
				this.synthesizedFormulas.get(envVarType).second = trace;
			}
		}
		finally {
			lock.unlock();
		}
	}
	
	/**
	 * When a worker finishes it uses this method to wake up the master thread.
	 */
	public void workerDone(final Map<String,String> envVarType) {
		try {
			this.lock.lock();
			// if for some weird reason there is no entry for this env var type, then we'll call it UNSAT
			if (!this.synthesizedFormulas.containsKey(envVarType)) {
				this.synthesizedFormulas.put(envVarType, new Utils.Pair<>(Formula.UNSAT(),null));
			}
			this.aWorkerIsDone.signalAll();
		}
		finally {
			lock.unlock();
		}
	}

	/**
	 * Synthesize one formula per "type" in <envVarTypes> and return all results that aren't UNSAT
	 * @return
	 */
	public Map<Map<String,String>, Utils.Pair<Formula,AlloyTrace>> synthesizeFormulas(FormulaSeparation formulaSep,
			Set<Map<String,String>> envVarTypes,
			AlloyTrace negTrace, final Map<Map<String,String>, List<AlloyTrace>> posTraces,
			TLC tlcComp, Set<String> internalActions,
			Map<String, Set<String>> sortElementsMap, Map<String, Map<String, Set<String>>> sortSetElementsMap,
			Map<String, List<String>> actionParamTypes,
			int maxActParamLen, Set<String> qvars, Set<Set<String>> legalEnvVarCombos,
			int curNumFluents, int cumNumPosTraces, String tlaRest, String cfgRest, String cfgPosTraces) {
		
		resetMemberVars();
		PerfTimer timer = new PerfTimer();
		int id = 0;
		for (final Map<String,String> evt : envVarTypes) {
			final List<AlloyTrace> evtPosTraces = posTraces.get(evt);
			final FormulaSynthWorker worker = new FormulaSynthWorker(this, formulaSep, evt, id++, negTrace, evtPosTraces,
					tlcComp, internalActions, sortElementsMap, sortSetElementsMap, actionParamTypes, maxActParamLen,
					qvars, legalEnvVarCombos, curNumFluents, cumNumPosTraces, tlaRest, cfgRest, cfgPosTraces);
			this.workers.add(worker);
		}
		
		// randomly shuffle the workers then reduce the number to make formula synthesis faster
		final int origNumWorkers = this.workers.size();
		final int numWorkers = Math.min(origNumWorkers, MAX_NUM_WORKERS);
		Collections.shuffle(this.workers, this.seed);
		while (this.workers.size() > numWorkers) {
			this.workers.remove(this.workers.size()-1);
		}
		System.out.println("Total # workers: " + origNumWorkers);
		System.out.println("# workers using: " + numWorkers);

		// book keeping vars
		boolean inShutdownCountdown = false;
		try {
			this.lock.lock();
			
			this.threadPool = Executors.newFixedThreadPool(MAX_NUM_THREADS);
			for (FormulaSynthWorker worker : workers) {
				this.threadPool.submit(worker);
			}
			
			long shutdownTime = Long.MAX_VALUE;
			while (this.synthesizedFormulas.size() < workers.size()) {
				try {
					this.aWorkerIsDone.await();
				}
				catch (InterruptedException e) {
					throw new RuntimeException("Aborting formula synth due to interruption!");
				}

				// shutdown count is reached! breaking will automatically kill all workers
				if (synthComplete || System.currentTimeMillis() >= shutdownTime) {
					final int numIncompleteWorkers = workers.size() - synthesizedFormulas.size();
					if (numIncompleteWorkers > 0) {
						System.out.println("Killing " + numIncompleteWorkers + " incomplete formula synth workers");
					}
					break;
				}
				
				// if we found an invariant, then return! breaking will automatically kill all workers
				final boolean foundInvariant = this.synthesizedFormulas
						.values()
						.stream()
						.anyMatch(p -> p.second != null && !p.second.hasError());
				if (foundInvariant) {
					final int numIncompleteWorkers = workers.size() - synthesizedFormulas.size();
					System.out.println("Found an invariant! Killling the " + numIncompleteWorkers + " remaining formula synth workers");
					break;
				}
				
				// in the case we have our first worker done, start a countdown until we kill the rest of the workers
				final boolean allUNSAT = this.synthesizedFormulas
						.values()
						.stream()
						.allMatch(f -> f.first.isUNSAT());
				if (!inShutdownCountdown && !allUNSAT) {
					// set a timer to shutdown all threads if the shutdown time is exceeded
					inShutdownCountdown = true;
					final long shutdownLength = SHUTDOWN_MULTIPLIER * timer.timeElapsed();
					shutdownTime = System.currentTimeMillis() + shutdownLength;
					new Thread() {
					    public void run() {
					        try {
								sleep(shutdownLength);
							} catch (InterruptedException e) {}
					        try {
						        lock.lock();
								synthComplete = true;
								aWorkerIsDone.signalAll();
					        }
					        finally {
					        	lock.unlock();
					        }
					    }
					}.start();
					
					// let the user know how much time is left
					final double maxTimeLeft = shutdownLength / 1000.0;
					System.out.println("First worker finished, shutdown count is " + maxTimeLeft + "s");
				}
			}
		}
		finally {
			this.synthComplete = true;
			this.lock.unlock();
			this.cleanUpWorkers();
		}
		
		System.out.println("Formula synthesis complete in " + timer.timeElapsedSeconds() + " seconds");
		return this.synthesizedFormulas;
	}
	
	private void cleanUpWorkers() {
		this.threadPool.shutdownNow();
		for (FormulaSynthWorker worker : this.workers) {
			worker.kill();
		}
		
		// also clean up temp files that the workers wrote to free up disk space
		try {
			Runtime runtime = Runtime.getRuntime();
			runtime.exec(new String[]{"sh", "-c", "rm -f " + TMP_DIR + "/alloy_heredoc*.als"});
			runtime.exec(new String[]{"sh", "-c", "rm -f " + TMP_DIR + "/kodkod*.log"});
			runtime.exec(new String[]{"sh", "-c", "rm -f " + TMP_DIR + "/tmp*.wcnf"});
		} catch (IOException e) {
			// nothing to do if this fails
		}
	}
	
	private void resetMemberVars() {
		this.synthesizedFormulas = new HashMap<>();
		this.workers = new ArrayList<>();
		this.synthComplete = false;
	}
}
