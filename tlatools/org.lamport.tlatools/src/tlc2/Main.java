package tlc2;

import java.util.ArrayList;
import java.util.List;

import cmu.isr.ts.LTS;
import cmu.isr.ts.lts.SafetyUtils;
import cmu.isr.ts.lts.ltsa.FSPWriter;
import lts.SymbolTable;
import recomp.AlloyTrace;
import recomp.Composition;
import recomp.Decomposition;
import recomp.Formula;
import recomp.FormulaSeparation;
import recomp.FormulaSynthWorker;
import recomp.RecompVerify;
import recomp.WeakestAssumption;
import recomp_naive.NaiveFormulaSeparation;

public class Main {
    public static void main(String[] args) {
		SymbolTable.init();
		
		if (!System.getenv().containsKey(FormulaSynthWorker.alsmFormulaSynthEnvVar)) {
			System.out.println("Please set the env var: " + FormulaSynthWorker.alsmFormulaSynthEnvVar);
			return;
		}
		
		// handle CLI args
		final boolean naive = hasFlag(args, "--naive");
		final boolean universal = hasFlag(args, "--universal");
		final int numWorkers = getNumWorkers(args);
		final int numSymActions = getIntArg(args, "--sym-actions", 5);
		final int formulaSize = getIntArg(args, "--formula-size", 7);
		final int numQuantifiers = getIntArg(args, "--quants", 3);
		final long negTraceCheckMinutes = getLongArg(args, "--neg-trace-check", 5L);
		final long posTraceCheckMinutes = getLongArg(args, "--pos-trace-check", 1L);
		final String workerHeapSize = getStrArg(args, "--heap", "6G");
		
		// experimental arg for extending the neg trace search
		final boolean extendedNegTraceSearch = hasFlag(args,"--ext-negt");
		
		// random seeds are not well supported
	    final long seed = hasArg(args,"--seed") ? Long.parseLong(getArg(args,"--seed")) : 0L; //System.nanoTime();
		
		// main business logic
    	if (args.length >= 5 && !naive) {
    		final String tlaComp = args[0];
    		final String cfgComp = args[1];
    		final String tlaRest = args[2];
    		final String cfgRest = args[3];
    		final String propFile = args[4];
    		final Formula sep =
    				new FormulaSeparation(tlaComp, cfgComp, tlaRest, cfgRest, propFile,
    						universal, numWorkers, numSymActions, formulaSize, numQuantifiers,
    						negTraceCheckMinutes, posTraceCheckMinutes, workerHeapSize,
    						extendedNegTraceSearch, seed)
    					.synthesizeSepInvariant();
    		final String formula = sep.toString();
    		
    		if (!formula.contains("UNSAT")) {
        		System.out.println("The following formula is a separating assumption:");
    		}
    		else {
        		System.out.println("Could not synthesize a spearating assumption. Here are the intermediate conjuncts:");
    		}
    		System.out.println(formula);
    	}
    	// run the naive version of the algorithm
    	else if (args.length >= 5 && naive) {
    		final String tlaComp = args[0];
    		final String cfgComp = args[1];
    		final String tlaRest = args[2];
    		final String cfgRest = args[3];
    		final String propFile = args[4];
    		final Formula sep =
    				new NaiveFormulaSeparation(tlaComp, cfgComp, tlaRest, cfgRest, propFile, extendedNegTraceSearch, seed)
    					.synthesizeSepInvariant();
    		final String formula = sep.toString();
    		
    		if (!formula.contains("UNSAT")) {
        		System.out.println("The following formula is a separating assumption:");
    		}
    		else {
        		System.out.println("Could not synthesize a spearating assumption. Here are the intermediate conjuncts:");
    		}
    		System.out.println(formula);
    	}
    	// special feature for making TLC print an action-based cex (trace)
    	else if (args.length == 3 && args[0].equals("--cex")) {
    		final String tla = args[1];
    		final String cfg = args[2];
    		final long timeout = 10000L; // 10000 min
    		final AlloyTrace trace = new FormulaSeparation(tla, cfg, tla, cfg, "none",
    				universal, numWorkers, numSymActions, formulaSize, numQuantifiers,
					negTraceCheckMinutes, posTraceCheckMinutes, workerHeapSize,
					extendedNegTraceSearch, seed)
    				.genCexTraceForCandSepInvariant(tla, cfg, "", 0, "", timeout);
    		System.out.println(trace);
    	}
    	else if (args.length == 3 && args[0].endsWith("--safe")) {
    		final String tla = args[1];
    		final String cfg = args[2];
    		TLC tlcCexReproducer = new TLC();
        	tlcCexReproducer.modelCheck(tla, cfg);
        	final LTS<Integer, String> lts = tlcCexReproducer.getLTSBuilder().toIncompleteDetAutIncludingAnErrorState();
        	final boolean isSafe = SafetyUtils.INSTANCE.ltsIsSafe(lts);
        	System.out.println("Is safe: " + isSafe);
    	}
    	else {
    		System.out.println("usage: carini <tlaComp> <cfgComp> <tlaRest> <cfgRest> <propFile> [flags]");
    		System.out.println("flags:");
    		System.out.println(" --navie: uses the naive (non-incremental) algorithm.");
    		System.out.println(" --universal: only searches for formulas with universal (forall) quantifiers.");
    		System.out.println(" --workers: the maximum number of formula synthesis workers.");
    		System.out.println(" --max-workers: the maximum number of formula synthesis workers will be: min(#cores on your machine, --max-workers)");
    		System.out.println(" --sym-actions: the maximum number of symbolic actions that can be used in synthesized fluents.");
    		System.out.println(" --formula-size: the maximum size of a synthesized formula.");
    		System.out.println(" --quants: the maximum number of quantifiers that can appear in a synthesized formula.");
    		System.out.println(" --neg-trace-check: timeout for checking for negative traces (in minutes).");
    		System.out.println(" --pos-trace-check: timeout for checking for positive traces (in minutes).");
    		System.out.println(" --heap: heap size for each worker, specified with a unit (e.g. the default value is '6G').");
    	}
    	System.exit(0);
    }
    
    private static int getNumWorkers(String[] args) {
    	final String numWorkersFlag = "--workers";
    	final String maxNumWorkersFlag = "--max-workers";
    	int numWorkers = Runtime.getRuntime().availableProcessors();
		if (hasArg(args, numWorkersFlag)) {
			final String strWorkers = getArg(args, numWorkersFlag);
			numWorkers = Integer.parseInt(strWorkers);
		}
		else if (hasArg(args, maxNumWorkersFlag)) {
			final String strMaxWorkers = getArg(args, maxNumWorkersFlag);
			final int maxWorkers = Integer.parseInt(strMaxWorkers);
			numWorkers = Math.min(numWorkers, maxWorkers);
		}
		else {
			// by default, we cap the maximum number of workers at 32
			final int maxWorkers = 32;
			numWorkers = Math.min(numWorkers, maxWorkers);
		}
		return numWorkers;
    }
    
    private static String getStrArg(String[] args, String param, String defaultValue) {
    	if (hasArg(args, param)) {
    		return getArg(args, param);
    	}
    	return defaultValue;
    }
    
    private static int getIntArg(String[] args, String param, int defaultValue) {
    	if (hasArg(args, param)) {
    		final String strValue = getArg(args, param);
    		return Integer.parseInt(strValue);
    	}
    	return defaultValue;
    }
    
    private static long getLongArg(String[] args, String param, long defaultValue) {
    	if (hasArg(args, param)) {
    		final String strValue = getArg(args, param);
    		return Long.parseLong(strValue);
    	}
    	return defaultValue;
    }
    
    private static String getArg(String[] args, final String param) {
    	int paramIdx = -1;
    	for (int i = 0; i < args.length; ++i) {
    		if (param.endsWith(args[i])) {
    			// the positional arg is right after the param flag
    			paramIdx = i + 1;
    			break;
    		}
    	}
    	Utils.assertTrue(paramIdx >= 0 && paramIdx < args.length, "Invalid use of the param flag: " + param);
    	return args[paramIdx];
    }
    
    private static boolean hasArg(String[] args, final String param) {
    	int paramIdx = -1;
    	for (int i = 0; i < args.length; ++i) {
    		if (param.endsWith(args[i])) {
    			// the positional arg is right after the param flag
    			paramIdx = i + 1;
    			break;
    		}
    	}
    	return paramIdx >= 0 && paramIdx < args.length;
    }
    
    private static boolean hasFlag(String[] args, final String flag) {
    	return Utils.toArrayList(args)
				.stream()
				.filter(s -> s.equals(flag))
				.count() > 0;
    }
}
