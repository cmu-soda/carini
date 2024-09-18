package recomp;

import java.io.IOException;
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
	private static final int MAX_NUM_THREADS = 25;
	
	private String globalFormula;
	private int winningWorkerId;
	private double winningTimeElapsedInSeconds;
	private int numWorkersDone;
	private Set<FormulaSynthWorker> workers;
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
	public void setFormula(final String formula, int workerId, double timeElapsedInSeconds) {
		try {
			this.lock.lock();
			++this.numWorkersDone;
			if (this.globalFormula.contains("UNSAT") && !formula.contains("UNSAT") && !formula.trim().isEmpty()) {
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
			TLC tlcSys, TLC tlcComp, Set<String> internalActions,
			Map<String, Set<String>> sortElementsMap, Map<String, List<String>> actionParamTypes,
			int maxActParamLen, Set<String> qvars, Set<Set<String>> legalEnvVarCombos,
			int curNumFluents) {
		
		resetMemberVars();
		PerfTimer timer = new PerfTimer();
		int id = 0;
		for (final Map<String,String> m : envVarTypes) {
			for (int numQuants = 1; numQuants <= qvars.size(); ++numQuants) {
				final FormulaSynthWorker worker = new FormulaSynthWorker(this, m, id++, negTrace, posTraces,
						tlcSys, tlcComp, internalActions, sortElementsMap, actionParamTypes, maxActParamLen,
						qvars, legalEnvVarCombos, curNumFluents, numQuants);
				this.workers.add(worker);
			}
		}

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
			runtime.exec(new String[]{"rm", "-f", "/tmp/alloy_heredoc*.als"});
			runtime.exec(new String[]{"rm", "-f", "/tmp/kodkod*.log"});
			runtime.exec(new String[]{"rm", "-f", "/tmp/tmp*.wcnf"});
		} catch (IOException e) {
			// nothing to do if this fails
		}
	}
	
	private void resetMemberVars() {
		this.globalFormula = "{\"formula\":\"UNSAT\"}";
		this.winningWorkerId = -1;
		this.winningTimeElapsedInSeconds = 0.0;
		this.numWorkersDone = 0;
		this.workers = new HashSet<>();
	}
}
