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
import recomp.FormulaSeparation;
import recomp.FormulaSynthWorker;
import recomp.RecompVerify;
import recomp.WeakestAssumption;

public class Main {
    public static void main(String[] args) {
		SymbolTable.init();
		
		if (!System.getenv().containsKey(FormulaSynthWorker.alsmFormulaSynthEnvVar)) {
			System.out.println("Please set the env var: " + FormulaSynthWorker.alsmFormulaSynthEnvVar);
			return;
		}
		
		// main business logic
    	if (args.length >= 5) {
    		final String tlaComp = args[0];
    		final String cfgComp = args[1];
    		final String tlaRest = args[2];
    		final String cfgRest = args[3];
    		final String propFile = args[4];
    		final long seed = args.length > 5 ? Long.parseLong(args[5]) : System.nanoTime();
    		final String formula = new FormulaSeparation(tlaComp, cfgComp, tlaRest, cfgRest, propFile, seed).synthesizeSepInvariant();
    		
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
    		final AlloyTrace trace = new FormulaSeparation(tla,cfg,tla,cfg,"none",0L)
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
    		System.out.println("usage: carini <tlaComp> <cfgComp> <tlaRest> <cfgRest> <propFile> [<randomSeed>]");
    	}
    	System.exit(0);
    }
    
    private static boolean hasFlag(String[] args, final String flag) {
    	return Utils.toArrayList(args)
				.stream()
				.filter(s -> s.equals(flag))
				.count() > 0;
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
}
