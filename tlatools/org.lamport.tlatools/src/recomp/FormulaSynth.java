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

public class FormulaSynth {
	public static final String maxNumWorkersEnvVar = "FSYNTH_MAX_NUM_WORKERS";
	private static final String TMP_DIR = System.getProperty("java.io.tmpdir");;
	private static final int MAX_NUM_THREADS = System.getenv(maxNumWorkersEnvVar) != null ? Integer.parseInt(System.getenv(maxNumWorkersEnvVar)) : 25;
	private static final int MAX_NUM_WORKERS = 15;
	
	private Map<Map<String,String>, Formula> synthesizedFormulas;
	private List<FormulaSynthWorker> workers;
	private ExecutorService threadPool;
	private Random seed;

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
	public void setFormula(final String formula, int workerId, final Map<String,String> envVarType, double timeElapsedInSeconds) {
		try {
			this.lock.lock();
			if (!formula.contains("UNSAT") && !formula.trim().isEmpty()) {
				this.synthesizedFormulas.put(envVarType, new Formula(formula));
			}
			else {
				// the thread may have crashed, rather than returned UNSAT. we treat both cases the same for now.
				this.synthesizedFormulas.put(envVarType, Formula.UNSAT());
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
			TLC tlcComp, Set<String> internalActions,
			Map<String, Set<String>> sortElementsMap, Map<String, Map<String, Set<String>>> sortSetElementsMap,
			Map<String, List<String>> actionParamTypes,
			int maxActParamLen, Set<String> qvars, Set<Set<String>> legalEnvVarCombos,
			int curNumFluents) {
		
		resetMemberVars();
		PerfTimer timer = new PerfTimer();
		int id = 0;
		for (final Map<String,String> evt : envVarTypes) {
			final List<AlloyTrace> evtPosTraces = posTraces.get(evt);
			final FormulaSynthWorker worker = new FormulaSynthWorker(this, evt, id++, negTrace, evtPosTraces,
					tlcComp, internalActions, sortElementsMap, sortSetElementsMap, actionParamTypes, maxActParamLen,
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
			for (FormulaSynthWorker worker : workers) {
				this.threadPool.submit(worker);
			}
			
			while (this.synthesizedFormulas.size() < workers.size()) {
				try {
					this.aWorkerIsDone.await();
				}
				catch (InterruptedException e) {}
			}
		}
		finally {
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
	}
}
