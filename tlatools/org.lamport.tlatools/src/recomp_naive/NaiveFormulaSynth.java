package recomp_naive;

import static org.junit.Assert.assertNotNull;

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

import recomp.AlloyTrace;
import recomp.Formula;
import tlc2.TLC;
import tlc2.Utils;

public class NaiveFormulaSynth {
	public static final String maxNumWorkersEnvVar = "FSYNTH_MAX_NUM_WORKERS";
	private static final String TMP_DIR = System.getProperty("java.io.tmpdir");
	private static final int MAX_NUM_THREADS = Runtime.getRuntime().availableProcessors();
	private static final int MAX_NUM_WORKERS = MAX_NUM_THREADS;
	
	private Formula synthesizedFormula;
	private List<NaiveFormulaSynthWorker> workers;
	private ExecutorService threadPool;
	private Random seed;

	private final Lock lock = new ReentrantLock();
	private final Condition aWorkerIsDone = lock.newCondition();
	
	public NaiveFormulaSynth(Random rseed) {
		resetMemberVars();
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
			if (this.synthesizedFormula == null) {
				// only modify <synthesizedFormulas> if it's before the shutdown time
				if (!formula.contains("UNSAT") && !formula.trim().isEmpty()) {
					this.synthesizedFormula = new Formula(formula);
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
	public Formula synthesizeFormulas(Set<Map<String,String>> envVarTypes,
			final Set<AlloyTrace> negTraces, final Set<AlloyTrace> posTraces,
			TLC tlcComp, Set<String> globalActions,
			Map<String, Set<String>> sortElementsMap, Map<String, Map<String, Set<String>>> sortSetElementsMap,
			Map<String, List<String>> actionParamTypes,
			int maxActParamLen, List<String> qvars, Set<Set<String>> legalEnvVarCombos,
			int curNumFluents) {
		
		resetMemberVars();
		int id = 0;
		for (final Map<String,String> evt : envVarTypes) {
			final NaiveFormulaSynthWorker worker = new NaiveFormulaSynthWorker(this, evt, id++, negTraces, posTraces,
					tlcComp, globalActions, sortElementsMap, sortSetElementsMap, actionParamTypes, maxActParamLen,
					qvars, legalEnvVarCombos, curNumFluents);
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
		
		try {
			this.lock.lock();
			
			this.threadPool = Executors.newFixedThreadPool(MAX_NUM_THREADS);
			for (NaiveFormulaSynthWorker worker : workers) {
				this.threadPool.submit(worker);
			}
			
			long shutdownTime = Long.MAX_VALUE;
			while (this.synthesizedFormula == null) {
				try {
					this.aWorkerIsDone.await();
				}
				catch (InterruptedException e) {
					throw new RuntimeException("Aborting formula synth due to interruption!");
				}
				
				// calculate the number of workers that are still running
				final int numIncompleteWorkers = workers.size() - (this.synthesizedFormula == null ? 0 : 1);

				// shutdown count is reached! breaking will automatically kill all workers
				if (this.synthesizedFormula != null || System.currentTimeMillis() >= shutdownTime) {
					if (numIncompleteWorkers > 0) {
						System.out.println("Killing " + numIncompleteWorkers + " incomplete formula synth workers");
					}
					break;
				}
			}
		}
		finally {
			this.lock.unlock();
			this.cleanUpWorkers();
		}
		
		return this.synthesizedFormula;
	}
	
	private void cleanUpWorkers() {
		this.threadPool.shutdownNow();
		for (NaiveFormulaSynthWorker worker : this.workers) {
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
		this.synthesizedFormula = null;
		this.workers = new ArrayList<>();
	}
}
