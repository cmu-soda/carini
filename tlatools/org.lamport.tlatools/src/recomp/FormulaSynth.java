package recomp;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
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
	
	private Set<String> synthesizedFormulas;
	private int winningWorkerId;
	private double winningTimeElapsedInSeconds;
	private int numWorkersDone;
	private Set<Map<String,String>> unsatEnvVarTypes;
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
			++this.numWorkersDone;
			if (!formula.contains("UNSAT") && !formula.trim().isEmpty()) {
				this.synthesizedFormulas.add(formula);
				this.winningWorkerId = workerId;
				this.winningTimeElapsedInSeconds = timeElapsedInSeconds;
			}
			else {
				// the thread may have crashed, rather than returned UNSAT. we treat both cases the same for now.
				this.unsatEnvVarTypes.add(envVarType);
			}
			// notify the master that this thread is done
			this.aWorkerIsDone.signalAll();
		}
		finally {
			lock.unlock();
		}
	}

	/**
	 * Synthesize a formula using MAX_NUM_THREADS. The first formula to return a satisfying
	 * formula "wins".
	 * @return
	 */
	public Set<Formula> synthesizeFormulas(Set<Map<String,String>> envVarTypes,
			AlloyTrace negTrace, List<AlloyTrace> posTraces,
			TLC tlcComp, Set<String> internalActions,
			Map<String, Set<String>> sortElementsMap, Map<String, Map<String, Set<String>>> sortSetElementsMap,
			Map<String, List<String>> actionParamTypes,
			int maxActParamLen, Set<String> qvars, Set<Set<String>> legalEnvVarCombos,
			int curNumFluents) {
		
		resetMemberVars();
		PerfTimer timer = new PerfTimer();
		int id = 0;
		for (final Map<String,String> m : envVarTypes) {
			final FormulaSynthWorker worker = new FormulaSynthWorker(this, m, id++, negTrace, posTraces,
					tlcComp, internalActions, sortElementsMap, sortSetElementsMap, actionParamTypes, maxActParamLen,
					qvars, legalEnvVarCombos, curNumFluents);
			this.workers.add(worker);
		}
		
		// randomly shuffle the workers then reduce the number to make formula synthesis faster
		final int origNumWorkers = this.workers.size();
		final int numWorkers = Math.min(origNumWorkers, 2*MAX_NUM_THREADS);
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
			
			while (this.numWorkersDone < workers.size()) {
				try {
					this.aWorkerIsDone.await();
				}
				catch (InterruptedException e) {}
				
				// remove any env var type from this round that returns UNSAT. this is an optimization to prevent
				// us from re-running workers (in a given round) that are guaranteed to return UNSAT. this modifies
				// the out-param envVarTypes!
				envVarTypes.removeAll(this.unsatEnvVarTypes);
			}
		}
		finally {
			this.lock.unlock();
			this.cleanUpWorkers();
		}
		
		System.out.println("Formula synthesis complete in " + timer.timeElapsedSeconds() + " seconds");
		
		// all formulas have been synthesized
		if (this.synthesizedFormulas.isEmpty()) {
			// all formulas are UNSAT
			return Set.of(Formula.UNSAT());
		}
		return this.synthesizedFormulas
				.stream()
				.map(f -> new Formula(f))
				.collect(Collectors.toSet());
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
		this.synthesizedFormulas = new HashSet<>();
		this.winningWorkerId = -1;
		this.winningTimeElapsedInSeconds = 0.0;
		this.numWorkersDone = 0;
		this.unsatEnvVarTypes = new HashSet<>();
		this.workers = new ArrayList<>();
	}
}
