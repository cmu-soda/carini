package recomp;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import cmu.isr.ts.LTS;
import net.automatalib.commons.util.Holder;
import net.automatalib.ts.TransitionSystem;
import net.automatalib.util.ts.traversal.TSTraversal;
import net.automatalib.util.ts.traversal.TSTraversalAction;
import net.automatalib.util.ts.traversal.TSTraversalVisitor;
import net.automatalib.words.Word;
import tlc2.Utils;

public class ExtendTraceVisitor<S> implements TSTraversalVisitor<S, String, S, Word<String>> {
	private static final int MAX_NUM_INTERNAL_ACTIONS = 200;
	private final AlloyTrace alsTrace;
	private final Set<String> globalActions;
	private Set<String> extensions;
	private int numInternalActionsSeen = 0;
	
	public ExtendTraceVisitor(AlloyTrace alsTrace, Set<String> globalActions) {
		this.alsTrace = alsTrace;
		this.globalActions = globalActions;
		this.extensions = new HashSet<>();
	}

	@Override
	public TSTraversalAction processInitial(S state, Holder<Word<String>> trace) {
		trace.value = Word.epsilon();
		return TSTraversalAction.EXPLORE;
	}

	@Override
	public TSTraversalAction processTransition(S src, Word<String> trace, String act, S tr, S dst, Holder<Word<String>> outTrace) {
		Utils.assertTrue(globalActionTraceSize(trace) <= this.alsTrace.size(), "Invalid trace size found in ExtendTraceVisitor");
		outTrace.value = trace.append(act);
		
		final boolean isGlobalAction = this.globalActions.contains(act.replaceAll("\\..*$", ""));
		
		// global actions
		if (isGlobalAction) {
			// the case where we've reached the end of the als trace, and <act> is an extension
			if (globalActionTraceSize(trace) == this.alsTrace.size()) {
				this.extensions.add(act);
				return TSTraversalAction.IGNORE;
			}
			
			// the case where we're still traversing the als trace
			final int idx = globalActionTraceSize(trace);
			final String nextAct = this.alsTrace.rawWord().get(idx);
			return act.equals(nextAct) ? TSTraversalAction.EXPLORE : TSTraversalAction.IGNORE;
		}
		// internal (non-global) actions
		else {
			// keep track of how many internal actions we've seen so the search is bounded
			if (this.numInternalActionsSeen > MAX_NUM_INTERNAL_ACTIONS) {
				return TSTraversalAction.IGNORE;
			}
			++numInternalActionsSeen;
			return TSTraversalAction.EXPLORE;
		}
		
	}

	@Override
	public boolean startExploration(S state, Word<String> trace) {
		return trace == null || globalActionTraceSize(trace) < this.alsTrace.size()+1;
	}
	
	public Set<String> getTraceExtensionsByOne(LTS<Integer,String> lts) {
		this.numInternalActionsSeen = 0;
		TSTraversal.breadthFirst((TransitionSystem<S,String,S>)lts, lts.getInputAlphabet(), (TSTraversalVisitor<S, String, S, Word<String>>)this);
		return this.extensions;
	}
	
	private int globalActionTraceSize(Word<String> trace) {
		return (int) trace.stream()
				.map(a -> a.replaceAll("\\..*$", "")) // get the base action
				.filter(a -> this.globalActions.contains(a))
				.count();
	}
}
