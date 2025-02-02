package tlc2;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import cmu.isr.assumption.WAHelper;
import cmu.isr.tolerance.utils.LtsUtils;
import cmu.isr.ts.DetLTS;
import cmu.isr.ts.LTS;
import cmu.isr.ts.MutableDetLTS;
import cmu.isr.ts.lts.CompactLTS;
import kotlin.Pair;
import kotlin.Triple;
import net.automatalib.automata.fsa.impl.compact.CompactNFA;
import net.automatalib.util.automata.builders.AutomatonBuilders;
import net.automatalib.words.impl.Alphabets;
import tlc2.tool.Action;
import tlc2.tool.TLCState;

// TODO addBadInitState() is not properly implemented!!
public class LTSBuilder {
	private Set<LTSBState> initStates = new HashSet<>();
	private Set<LTSBState> allStates = new HashSet<>();
	private Set<Triple<LTSBState,String,LTSBState>> goodTransitions = new HashSet<>();
	private Set<Pair<LTSBState,String>> badTransitions = new HashSet<>();
	private Set<String> allActions = new HashSet<>();
	private boolean badInitState = false;

	// we keep track of partial transitions so we can detect LTSs that aren't incomplete deterministic automata
	private Set<Pair<LTSBState,String>> partialTransitions = new HashSet<>();


	public int size() {
		return this.allStates.size();
	}

    public void addInitState(final TLCState s) {
		final LTSBState lbs = new LTSBState(s);
    	this.initStates.add(lbs);
    	this.allStates.add(lbs);
    }

    public void addBadInitState(final TLCState s) {
    	this.badInitState = true;
    }

    public void addState(final TLCState s) {
		final LTSBState lbs = new LTSBState(s);
    	this.allStates.add(lbs);
    }

    public void addTransition(final TLCState src, final Action act, final TLCState dst) {
    	final LTSBState lbsSrc = new LTSBState(src);
    	final String strAct = act.actionNameWithParams();
    	final LTSBState lbsDst = new LTSBState(dst);
    	final Triple<LTSBState,String,LTSBState> transition = new Triple<>(lbsSrc, strAct, lbsDst);
    	
    	if (!this.goodTransitions.contains(transition)) {
        	this.allActions.add(strAct);
        	this.goodTransitions.add(transition);
        	
        	// ensures that we construct only incomplete deterministic automata
        	final Pair<LTSBState,String> partial = new Pair<>(lbsSrc, strAct);
        	//Utils.exitAssert(!partialTransitions.contains(partial), "The current component is NOT an incomplete deterministic automata!");
        	partialTransitions.add(partial);
        	
        	// actually, we can just ignore this transition. it's fine to merge all transitions into a bad one in this case.
        	// to ignore this properly we would need to check in the 'if' on line 63, otherwise we'll add the transition to goodTransitions
        	// and to partialTransitions.
        	//Utils.exitAssert(!badTransitions.contains(partial), "The current component is NOT an incomplete deterministic automata!");
    	}
    }

    public void addTransitionToErr(final TLCState src, final Action act) {
    	final LTSBState lbsSrc = new LTSBState(src);
    	final String strAct = act.actionNameWithParams();
    	final Pair<LTSBState,String> partial = new Pair<>(lbsSrc, strAct);
    	
    	if (!this.badTransitions.contains(partial)) {
        	this.allActions.add(strAct);
        	this.badTransitions.add(partial);

        	// actually, this is unneeded. we can replace it with the commented out code below!
        	//Utils.exitAssert(!partialTransitions.contains(partial), "The current component is NOT an incomplete deterministic automata!");
        	/*if (partialTransitions.contains(partial)) {
        		this.partialTransitions.remove(partial);
        		// need to somehow implement the line of code below efficiently, probably just this.goodTransitions.stream()
        		//this.goodTransitions.remove(new Triple<>(lbsSrc, strAct, lbsDst));
        	}*/
    	}
    }

    public LTS<Integer, String> toIncompleteDetAutIncludingAnErrorState() {
    	CompactNFA<String> compactNFA = AutomatonBuilders.newNFA(Alphabets.fromCollection(this.allActions)).create();
    	
    	if (this.badInitState) {
    		compactNFA.addInitialState(false);
    	}
    	else {
        	final Integer ltsErrState = compactNFA.addState(false);
        	
        	Map<LTSBState, Integer> lbsToLtsStates = new HashMap<>();
        	for (final LTSBState lbsState : this.allStates) {
        		final boolean isInitState = this.initStates.contains(lbsState);
    			final int ltsState = isInitState ? compactNFA.addInitialState(true) : compactNFA.addState(true);
    			lbsToLtsStates.put(lbsState, ltsState);
        	}

        	for (final Triple<LTSBState,String,LTSBState> tr : this.goodTransitions) {
        		final Integer src = lbsToLtsStates.get(tr.getFirst());
        		final String act = tr.getSecond();
        		final Integer dst = lbsToLtsStates.get(tr.getThird());
        		compactNFA.addTransition(src, act, dst);
        	}

        	for (final Pair<LTSBState,String> tr : this.badTransitions) {
        		final Integer src = lbsToLtsStates.get(tr.getFirst());
        		final String act = tr.getSecond();
        		compactNFA.addTransition(src, act, ltsErrState);
        	}
    	}

    	return new CompactLTS<String>(compactNFA);
    }

    public LTS<Integer, String> toIncompleteDetAutWithoutAnErrorState() {
    	Utils.assertTrue(this.badTransitions.size() == 0, "Called toNFAWithoutAnErrorState() on an unsafe LTS!");
    	CompactNFA<String> compactNFA = AutomatonBuilders.newNFA(Alphabets.fromCollection(this.allActions)).create();
    	
    	if (!this.badInitState) {
        	Map<LTSBState, Integer> lbsToLtsStates = new HashMap<>();
        	for (final LTSBState lbsState : this.allStates) {
        		final boolean isInitState = this.initStates.contains(lbsState);
    			final int ltsState = isInitState ? compactNFA.addInitialState(true) : compactNFA.addState(true);
    			lbsToLtsStates.put(lbsState, ltsState);
        	}

        	for (final Triple<LTSBState,String,LTSBState> tr : this.goodTransitions) {
        		final Integer src = lbsToLtsStates.get(tr.getFirst());
        		final String act = tr.getSecond();
        		final Integer dst = lbsToLtsStates.get(tr.getThird());
        		compactNFA.addTransition(src, act, dst);
        	}
    	}

    	return new CompactLTS<String>(compactNFA);
    }
    
    
    private static class LTSBState {
    	private final long sid;
    	
    	public LTSBState(final TLCState s) {
    		sid = s.fingerPrint();
    	}
    	
    	@Override
    	public boolean equals(Object o) {
    		if (o instanceof LTSBState) {
    			final LTSBState other = (LTSBState) o;
    			return this.sid == other.sid;
    		}
    		return false;
    	}
    	
    	@Override
    	public int hashCode() {
    		return Long.hashCode(this.sid);
    	}
    }
}