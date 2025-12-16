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
	private static final String TMP_DIR = System.getProperty("java.io.tmpdir");
	private static final long SHUTDOWN_MULTIPLIER = 2L;
	private static final long MIN_SHUTDOWN_TIME = 1000L * 30L; // 30 seconds
	
	private Map<Map<String,String>, Formula> synthesizedFormulas;
	private List<FormulaSynthWorker> workers;
	private ExecutorService threadPool;
	private Random seed;
	private boolean synthComplete;

	private final int maxNumWorkersPerBatch;
	private final Lock lock = new ReentrantLock();
	private final Condition aWorkerIsDone = lock.newCondition();
	
	public FormulaSynth(int numWorkers, Random rseed) {
		resetMemberVars();
		this.maxNumWorkersPerBatch = numWorkers;
		this.seed = rseed;
	}
	
	/**
	 * Manually synchronized
	 * @param formula
	 */
	public void setFormula(final String formula, int workerId, final Map<String,String> envVarType, double timeElapsedInSeconds) {
		try {
			this.lock.lock();
			// only modify <synthesizedFormulas> if it's before the shutdown time
			if (!this.synthComplete) {
				// only modify <synthesizedFormulas> if it's before the shutdown time
				if (!formula.contains("UNSAT") && !formula.trim().isEmpty()) {
					this.synthesizedFormulas.put(envVarType, new Formula(formula));
				}
				else {
					// the thread may have crashed, rather than returned UNSAT. we treat both cases the same for now.
					this.synthesizedFormulas.put(envVarType, Formula.UNSAT());
				}
			}
			// notify the master that this thread is done
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
	public Map<Map<String,String>, Formula> synthesizeFormulas(Set<Map<String,String>> envVarTypes,
			AlloyTrace negTrace, final Map<Map<String,String>, List<AlloyTrace>> posTraces,
			TLC tlcComp, Set<String> globalActions,
			Map<String, Set<String>> sortElementsMap, Map<String, Map<String, Set<String>>> sortSetElementsMap,
			Map<String, List<String>> actionParamTypes,
			int maxActParamLen, List<String> qvars, Set<Set<String>> legalEnvVarCombos, int curNumFluents,
			boolean universal, int numSymActs, int numTargets, int formulaSize, String workerHeapSize) {
		
		resetMemberVars();
		PerfTimer timer = new PerfTimer();
		int id = 0;
		for (final Map<String,String> evt : envVarTypes) {
			final List<AlloyTrace> evtPosTraces = posTraces.get(evt);
			final FormulaSynthWorker worker = new FormulaSynthWorker(this, evt, id++, negTrace, evtPosTraces,
					tlcComp, globalActions, sortElementsMap, sortSetElementsMap, actionParamTypes, maxActParamLen,
					qvars, legalEnvVarCombos, curNumFluents,
					universal, numSymActs, numTargets, formulaSize, workerHeapSize);
			this.workers.add(worker);
		}
		
		// randomly shuffle the workers then reduce the number to make formula synthesis faster
		final int origNumWorkers = this.workers.size();
		final int numWorkers = Math.min(origNumWorkers, maxNumWorkersPerBatch);
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
			
			this.threadPool = Executors.newFixedThreadPool(numWorkers);
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
				
				// calculate the number of workers that are still running
				final int numIncompleteWorkers = workers.size() - synthesizedFormulas.size();

				// shutdown count is reached! breaking will automatically kill all workers
				if (synthComplete || System.currentTimeMillis() >= shutdownTime) {
					if (numIncompleteWorkers > 0) {
						System.out.println("Killing " + numIncompleteWorkers + " incomplete formula synth workers");
					}
					break;
				}
				
				// in the case we have our first worker done, start a countdown until we kill the rest of the workers
				final boolean allUNSAT = this.synthesizedFormulas
						.values()
						.stream()
						.allMatch(f -> f.isUNSAT());
				if (!inShutdownCountdown && !allUNSAT) {
					// set a timer to shutdown all threads if the shutdown time is exceeded
					inShutdownCountdown = true;
					final long shutdownLength = Math.max(SHUTDOWN_MULTIPLIER * timer.timeElapsed(), MIN_SHUTDOWN_TIME);
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

				// disabling this "short circuit" optimization code for now.
				/*
				// if more than half of the workers have come back as UNSAT, then we will assume that all workers
				// will come back UNSAT. this is a speed optimization.
				if (allUNSAT && numIncompleteWorkers < numWorkers/2.0) {
					System.out.println("No formulas synthesized and more than half of the workers returned UNSAT; aborting formula synth");
					System.out.println("Killing " + numIncompleteWorkers + " incomplete formula synth workers");
					break;
				}*/
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
