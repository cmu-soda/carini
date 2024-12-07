package tlc2;

import java.util.ArrayList;
import java.util.List;

import cmu.isr.ts.LTS;
import cmu.isr.ts.lts.ltsa.FSPWriter;
import lts.SymbolTable;
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
		
    	if (args.length >= 7) {
    		final String tlaComp = args[0];
    		final String cfgComp = args[1];
    		final String tlaRest = args[2];
    		final String cfgRest = args[3];
    		final String tlaSys = args[4];
    		final String cfgSys = args[5];
    		final String propFile = args[6];
    		final long seed = args.length > 7 ? Long.parseLong(args[7]) : System.nanoTime();
    		final String formula = new FormulaSeparation(tlaComp, cfgComp, tlaRest, cfgRest, tlaSys, cfgSys, propFile, seed).synthesizeSepInvariant();
    		
    		if (!formula.contains("UNSAT")) {
        		System.out.println("The following formula is a separating assumption:");
    		}
    		else {
        		System.out.println("Could not synthesize a spearating assumption. Here are the intermediate conjuncts:");
    		}
    		System.out.println(formula);
    	}
    	else {
    		System.out.println("usage: carini <tlaComp> <cfgComp> <tlaRest> <cfgRest> <tlaSys> <cfgSys> <propFile> [<randomSeed>]");
    	}
    	System.exit(0);
    }
    
    private static void calc(String[] args) {
    	if (args.length >= 4) {
    		final String tlaSys = args[0];
    		final String cfgSys = args[1];
    		final String tlaComp = args[2];
    		final String cfgComp = args[3];
    		//final String output = FormulaSeparation.isCandSepInvariant(tlaSys, cfgSys, tlaComp, cfgComp, "", "");
    		//System.out.println(output);
    		
    		//final boolean decompose = hasFlag(args, "--decomp");
    		//final boolean weakestAssumption = hasFlag(args, "--wa");
    		/*
    		if (decompose) {
    			// write a config without any invariants / properties
    	    	final String noInvsCfg = "no_invs.cfg";
    	    	Utils.writeFile(noInvsCfg, "SPECIFICATION Spec");
    	    	
    			// only decompose the spec. this is primarily used as pre-processing for the parallel algorithm
    			final List<String> components = Decomposition.decompAll(tla, cfg);
    			final List<String> trimmedComponents = Composition.orderedTrimmedComponents(tla, cfg, components);
    		 	System.out.println(String.join(",", trimmedComponents));
    		}
    		else if (weakestAssumption) {
    			//final LTS<Integer, String> wa = WeakestAssumption.calc(tla, cfg);
    	    	//FSPWriter.INSTANCE.write(System.out, wa);
    	    	//System.out.println();
    			final String symWA = WeakestAssumption.calcSymbolic(tla, cfg);
    			System.out.println(symWA);
    		}
    		else {
    			// run recomp-verify
        		final boolean verbose = hasFlag(args, "--verbose");
        		final boolean custom = hasFlag(args, "--cust");
        		final boolean naive = hasFlag(args, "--naive");
        		//final boolean heuristic = !custom && !naive;
        		final String recompFile = custom ? positionalArg(args, "--cust") : "";
        		
        		// TODO ian this is lazy
        		Utils.assertTrue(!custom || !recompFile.isEmpty(), "--cust must be followed by a recomp file!");
        		Utils.assertTrue(!(custom && naive), "--custom and --naive are mutually exclusive options!");
        		
        		final String recompStrategy = custom ? "CUSTOM" : naive ? "NAIVE" : "HEURISTIC";
        		RecompVerify.recompVerify(tla, cfg, recompStrategy, recompFile, verbose);
    		}*/
    	}
    	
    	// invalid args, display usage
    	else {
    		System.out.println("usage1: recomp-verify <spec> <cfg> [--naive] [--cust <recomp-file>] [--verbose]\n"
    				+ "usage2: recomp-verify <spec> <cfg> --decomp\n"
    				+ "* in usage1: --naive and --cust are mutually exclusive");
    	}
    }
    
    private static boolean hasFlag(String[] args, final String flag) {
    	return Utils.toArrayList(args)
				.stream()
				.filter(s -> s.equals(flag))
				.count() > 0;
    }
    
    private static String positionalArg(String[] args, final String param) {
    	int paramIdx = -1;
    	for (int i = 0; i < args.length; ++i) {
    		if (param.endsWith(args[i])) {
    			// the positional arg is right after the param flag
    			paramIdx = i + 1;
    		}
    	}
    	Utils.assertTrue(paramIdx >= 0 && paramIdx < args.length, "Invalid use of the param flag: " + param);
    	return args[paramIdx];
    }
}
