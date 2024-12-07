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

public class InitTraceVisitor<S,I> implements TSTraversalVisitor<S, I, S, Word<I>> {
	private final int targetSize;
	private Word<I> initTrace;
	private Set<S> visited;
	
	public InitTraceVisitor(int sz) {
		this.targetSize = sz;
		this.initTrace = Word.epsilon();
		this.visited = new HashSet<>();
	}

	@Override
	public TSTraversalAction processInitial(S state, Holder<Word<I>> trace) {
		this.visited.add(state);
		this.initTrace = Word.epsilon();
		trace.value = Word.epsilon();
		return TSTraversalAction.EXPLORE;
	}

	@Override
	public TSTraversalAction processTransition(S src, Word<I> trace, I act, S tr, S dst, Holder<Word<I>> outTrace) {
		outTrace.value = trace.append(act);
        this.initTrace = outTrace.value;
        if (this.initTrace.size() >= targetSize) {
        	return TSTraversalAction.ABORT_TRAVERSAL;
        }
        
        final boolean foundNewState = !this.visited.contains(dst);
        this.visited.add(dst);
        return foundNewState ? TSTraversalAction.EXPLORE : TSTraversalAction.IGNORE;
	}

	@Override
	public boolean startExploration(S state, Word<I> trace) {
		return trace == null || trace.size() < targetSize;
	}
	
	public List<I> findAnInitTrace(LTS<Integer,I> lts) {
		TSTraversal.depthFirst((TransitionSystem<S,I,S>)lts, lts.getInputAlphabet(), (TSTraversalVisitor<S, I, S, Word<I>>)this);
		//TSTraversal.depthFirst((TransitionSystem<S,I,I>)lts, lts.getInputAlphabet(), this);
		return this.initTrace.asList();
	}
}
