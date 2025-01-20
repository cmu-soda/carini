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
	private final AlloyTrace alsTrace;
	private Set<String> extensions;
	
	public ExtendTraceVisitor(AlloyTrace alsTrace) {
		this.alsTrace = alsTrace;
		this.extensions = new HashSet<>();
	}

	@Override
	public TSTraversalAction processInitial(S state, Holder<Word<String>> trace) {
		trace.value = Word.epsilon();
		return TSTraversalAction.EXPLORE;
	}

	@Override
	public TSTraversalAction processTransition(S src, Word<String> trace, String act, S tr, S dst, Holder<Word<String>> outTrace) {
		Utils.assertTrue(trace.size() <= this.alsTrace.size(), "Invalid trace size found in ExtendTraceVisitor");
		outTrace.value = trace.append(act);
		
		// the case where we've reached the end of the als trace, and <act> is an extension
		if (trace.length() == this.alsTrace.size()) {
			this.extensions.add(act);
			return TSTraversalAction.IGNORE;
		}
		
		// the case where we're still traversing the als trace
		final int idx = trace.length();
		final String nextAct = this.alsTrace.rawWord().get(idx);
		return act.equals(nextAct) ? TSTraversalAction.EXPLORE : TSTraversalAction.IGNORE;
	}

	@Override
	public boolean startExploration(S state, Word<String> trace) {
		return trace == null || trace.size() < this.alsTrace.size()+1;
	}
	
	public Set<String> getTraceExtensionsByOne(LTS<Integer,String> lts) {
		TSTraversal.breadthFirst((TransitionSystem<S,String,S>)lts, lts.getInputAlphabet(), (TSTraversalVisitor<S, String, S, Word<String>>)this);
		return this.extensions;
	}
}
