package recomp;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

import tlc2.TLC;

public class FormulaSynth {
	public static final String maxNumWorkersEnvVar = "FSYNTH_MAX_NUM_WORKERS";
	private static final int MAX_NUM_THREADS = System.getenv(maxNumWorkersEnvVar) != null ? Integer.parseInt(System.getenv(maxNumWorkersEnvVar)) : 25;
	
	private String globalFormula;
	private int winningWorkerId;
	private double winningTimeElapsedInSeconds;
	private int numWorkersDone;
	private Set<Map<String,String>> unsatEnvVarTypes;
	private List<FormulaSynthWorker> workers;
	private ExecutorService threadPool;

	private final Lock lock = new ReentrantLock();
	private final Condition aWorkerIsDone = lock.newCondition();
	
	public FormulaSynth() {
		resetMemberVars();
	}
	
	/**
	 * Manually synchronized
	 * @param formula
	 */
	public void setFormula(final String formula, int workerId, Map<String,String> envVarType, double timeElapsedInSeconds) {
		try {
			this.lock.lock();
			++this.numWorkersDone;
			if (formula.contains("UNSAT")) {
				this.unsatEnvVarTypes.add(envVarType);
			}
			else if (this.globalFormula.contains("UNSAT") && !formula.trim().isEmpty()) {
				this.globalFormula = formula;
				this.winningWorkerId = workerId;
				this.winningTimeElapsedInSeconds = timeElapsedInSeconds;
			}
			// no matter what, notify the master that this thread is done
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
	public Formula synthesizeFormula(Set<Map<String,String>> envVarTypes,
			AlloyTrace negTrace, List<AlloyTrace> posTraces,
			TLC tlcComp, Set<String> internalActions,
			Map<String, Set<String>> sortElementsMap, Map<String, List<String>> actionParamTypes,
			int maxActParamLen, Set<String> qvars, Set<Set<String>> legalEnvVarCombos,
			int curNumFluents) {
		
		resetMemberVars();
		PerfTimer timer = new PerfTimer();
		int id = 0;
		for (final Map<String,String> m : envVarTypes) {
			final FormulaSynthWorker worker = new FormulaSynthWorker(this, m, id++, negTrace, posTraces,
					tlcComp, internalActions, sortElementsMap, actionParamTypes, maxActParamLen,
					qvars, legalEnvVarCombos, curNumFluents);
			this.workers.add(worker);
		}
		Collections.shuffle(this.workers);
		System.out.println("Total # synth jobs: " + this.workers.size());

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
				
				final Formula formula = new Formula(this.globalFormula);
				if (!formula.isUNSAT()) {
					System.out.println("Formula synthesis info:\n"
							+ "  overall (multithread) time: " + timer.timeElapsedSeconds() + " seconds\n"
							+ "  winning worker id: " + this.winningWorkerId + "\n"
							+ "  winning worker time: " + this.winningTimeElapsedInSeconds + " seconds");
					return formula;
				}
			}
		}
		finally {
			this.lock.unlock();
			this.cleanUpWorkers();
		}

		// if we reach this point it means that we could not synthesize a formula
		return Formula.UNSAT();
	}
	
	private void cleanUpWorkers() {
		this.threadPool.shutdownNow();
		for (FormulaSynthWorker worker : this.workers) {
			worker.kill();
		}
		
		// also clean up temp files that the workers wrote to free up disk space
		try {
			Runtime runtime = Runtime.getRuntime();
			runtime.exec(new String[]{"sh", "-c", "rm -f /tmp/alloy_heredoc*.als"});
			runtime.exec(new String[]{"sh", "-c", "rm -f /tmp/kodkod*.log"});
			runtime.exec(new String[]{"sh", "-c", "rm -f /tmp/tmp*.wcnf"});
		} catch (IOException e) {
			// nothing to do if this fails
		}
	}
	
	private void resetMemberVars() {
		this.globalFormula = "{\"formula\":\"UNSAT\"}";
		this.winningWorkerId = -1;
		this.winningTimeElapsedInSeconds = 0.0;
		this.numWorkersDone = 0;
		this.unsatEnvVarTypes = new HashSet<>();
		this.workers = new ArrayList<>();
	}
}
