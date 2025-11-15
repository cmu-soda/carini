package recomp;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import tlc2.Utils;

public class AlloyTrace {
	private final boolean hasError;
	private final String name;
	private final String ext;
	private final int lastIdx;
	private final String alloyLastIdx;
	private final String alloyLastStateIdx;
	private final String alloyTrace;
	private final List<String> rawTrace;
	private final List<String> sanitizedTrace;
	private final List<String> tlaTrace;
	private final Set<Utils.Pair<String,String>> traceSet;
	private final int size;
	private final Set<String> globalActions; // TODO keeping a copy of the globalActions is hacky
	
	public AlloyTrace() {
		this.hasError = false;
		this.name = null;
		this.ext = null;
		this.lastIdx = -1;
		this.alloyLastIdx = null;
		this.alloyLastStateIdx = null;
		this.alloyTrace = null;
		this.rawTrace = null;
		this.sanitizedTrace = null;
		this.tlaTrace = null;
		this.traceSet = null;
		this.size = 0;
		this.globalActions = null;
	}
	
	public AlloyTrace(final List<String> rawTrace, final List<String> sanitizedTrace, final String name, final String ext,
			final Set<String> globalActions) {
		final int lastIdx = sanitizedTrace.size() - 1;
		final String alloyLastIdx = "T" + lastIdx;
		final String alloyLastStateIdx = "T" + sanitizedTrace.size();
		final String rawAlloyTrace = IntStream.range(0, sanitizedTrace.size())
				.mapToObj(i -> {
					final String time = "T" + i;
					final String act = sanitizedTrace.get(i);
					return time + "->" + act;
				})
				.collect(Collectors.joining(" + "));
		final String alloyTrace = "(" + rawAlloyTrace + ")";
		
		this.traceSet = IntStream.range(0, sanitizedTrace.size())
				.mapToObj(i -> {
					final String time = "T" + i;
					final String act = sanitizedTrace.get(i);
					return new Utils.Pair<>(time,act);
				})
				.collect(Collectors.toSet());
		
		// create a trace in TLA+ format
		final List<String> tlaTrace = rawTrace
				.stream()
				.map(a -> {
					final List<String> actParts = Utils.toArrayList(a.split("\\."));
					Utils.assertTrue(actParts.size() >= 1, "eror splitting an action!");
					final String act = actParts.get(0);
					final List<String> params = actParts.subList(1, actParts.size());
					return params.size() == 0 ? act : act + "(" + String.join(",", params) + ")";
				})
				.collect(Collectors.toList());
		
		this.hasError = true;
		this.name = name;
		this.ext = ext;
		this.lastIdx = lastIdx;
		this.alloyLastIdx = alloyLastIdx;
		this.alloyLastStateIdx = alloyLastStateIdx;
		this.alloyTrace = alloyTrace;
		this.sanitizedTrace = sanitizedTrace;
		this.tlaTrace = tlaTrace;
		this.rawTrace = rawTrace;
		this.size = sanitizedTrace.size();
		this.globalActions = globalActions;
	}
	
	public boolean hasError() {
		return this.hasError;
	}
	
	public String name() {
		return this.name;
	}
	public String ext() {
		return this.ext;
	}
	
	public int lastIdx() {
		return this.lastIdx;
	}
	
	public String alloyLastIdx() {
		return this.alloyLastIdx;
	}
	
	public String alloyLastStateIdx() {
		return this.alloyLastStateIdx;
	}
	
	public String alloyTrace() {
		return this.alloyTrace;
	}
	
	public List<String> sanitizedTrace() {
		return this.sanitizedTrace;
	}
	
	public List<String> tlaTrace() {
		return this.tlaTrace;
	}
	
	public List<String> rawTrace() {
		return this.rawTrace;
	}
	
	public String finalBaseAction() {
		final String finalAction = this.tlaTrace.get(this.tlaTrace.size()-1);
		return finalAction.replaceAll("\\(.*$", "");
	}
	
	public int size() {
		return this.size;
	}
	
	public boolean isEmpty() {
		return this.size == 0;
	}
	
	public AlloyTrace cutToLen(int len) {
		return cutToLen(len, this.name, this.ext);
	}
	
	public AlloyTrace cutToLen(int len, final String newName, final String newExt) {
		final List<String> cutRawTrace = this.rawTrace
				.stream()
				.limit(len)
				.collect(Collectors.toList());
		final List<String> cutSanitizedTrace = this.sanitizedTrace
				.stream()
				.limit(len)
				.collect(Collectors.toList());
		return new AlloyTrace(cutRawTrace, cutSanitizedTrace, newName, newExt, this.globalActions);
	}
	
	public AlloyTrace newName(final String newName, final String newExt) {
		return new AlloyTrace(this.rawTrace, this.sanitizedTrace, newName, newExt, this.globalActions);
	}
	
	public AlloyTrace restrictToAlphabet(final Set<String> alphabet) {
		// figure out which indices in the trace are a part of the alphabet
		// we assume that the alphabet contains abstract actions
		final Set<Integer> alphabetActIdxs = IntStream.range(0, rawTrace.size())
				.filter(i -> {
					final String act = rawTrace.get(i);
					final String abstractAct = act.replaceAll("\\..*$", "");
					return alphabet.contains(abstractAct);
				})
				.mapToObj(i -> Integer.valueOf(i))
				.collect(Collectors.toSet());
		
		// restrict the traces
		final List<String> restrictedRawTrace = IntStream.range(0, rawTrace.size())
				.filter(i -> alphabetActIdxs.contains(i))
				.mapToObj(i -> rawTrace.get(i))
				.collect(Collectors.toList());
		final List<String> restrictedSanitizedTrace = IntStream.range(0, sanitizedTrace.size())
				.filter(i -> alphabetActIdxs.contains(i))
				.mapToObj(i -> sanitizedTrace.get(i))
				.collect(Collectors.toList());
		
		return new AlloyTrace(restrictedRawTrace, restrictedSanitizedTrace, name, ext, globalActions);
	}
	
	public String sigString() {
		return "one sig " + this.name + " extends " + this.ext + " {} {}";
		/*return "one sig " + this.name + " extends " + this.ext + " {} {\n"
			+ "	lastIdx = " + this.alloyLastIdx + "\n"
			+ "	path = " + this.path + "\n"
			+ "}";*/
	}
	
	public boolean contains(final AlloyTrace other) {
		return this.traceSet.containsAll(other.traceSet);
	}
	
	@Override
	public String toString() {
		return this.name + " (" + this.ext + "): " + this.alloyTrace;
	}
	
	@Override
	public boolean equals(Object o) {
		if (!(o instanceof AlloyTrace)) {
			return false;
		}
		AlloyTrace other = (AlloyTrace) o;
		if (this.sanitizedTrace == null && other.sanitizedTrace != null) {
			return false;
		}
		if (this.sanitizedTrace != null && other.sanitizedTrace == null) {
			return false;
		}
		// the == covers the case when this.trace and other.trace are both null
		return (this.sanitizedTrace == other.sanitizedTrace) || (this.sanitizedTrace.equals(other.sanitizedTrace));
	}
	
	@Override
	public int hashCode() {
		if (this.sanitizedTrace == null) {
			return 0;
		}
		return this.sanitizedTrace.hashCode();
	}
}
