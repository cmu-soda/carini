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
	private final String path;
	private final List<String> trace;
	private final List<String> tlaTrace;
	private final List<String> rawWord;
	private final Set<Utils.Pair<String,String>> traceSet;
	private final int size;
	
	public AlloyTrace() {
		this.hasError = false;
		this.name = null;
		this.ext = null;
		this.lastIdx = -1;
		this.alloyLastIdx = null;
		this.path = null;
		this.trace = null;
		this.tlaTrace = null;
		this.rawWord = null;
		this.traceSet = null;
		this.size = 0;
	}
	
	public AlloyTrace(final List<String> trace, final List<String> tlaTrace, final List<String> rawWord, final String name, final String ext) {
		final int lastIdx = trace.size() - 1;
		final String alloyLastIdx = "T" + lastIdx;
		final String path = IntStream.range(0, trace.size())
				.mapToObj(i -> {
					final String time = "T" + i;
					final String act = trace.get(i);
					return time + "->" + act;
				})
				.collect(Collectors.joining(" + "));
		final String pathParens = "(" + path + ")";
		
		this.traceSet = IntStream.range(0, trace.size())
				.mapToObj(i -> {
					final String time = "T" + i;
					final String act = trace.get(i);
					return new Utils.Pair<>(time,act);
				})
				.collect(Collectors.toSet());
		
		this.hasError = true;
		this.name = name;
		this.ext = ext;
		this.lastIdx = lastIdx;
		this.alloyLastIdx = alloyLastIdx;
		this.path = pathParens;
		this.trace = trace;
		this.tlaTrace = tlaTrace;
		this.rawWord = rawWord;
		this.size = trace.size();
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
	
	public String path() {
		return this.path;
	}
	
	public List<String> trace() {
		return this.trace;
	}
	
	public List<String> tlaTrace() {
		return this.tlaTrace;
	}
	
	public List<String> rawWord() {
		return this.rawWord;
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
		final List<String> cutTrace = this.trace
				.stream()
				.limit(len)
				.collect(Collectors.toList());
		final List<String> cutTlaTrace = this.tlaTrace
				.stream()
				.limit(len)
				.collect(Collectors.toList());
		final List<String> cutRawWord = this.rawWord
				.stream()
				.limit(len)
				.collect(Collectors.toList());
		return new AlloyTrace(cutTrace, cutTlaTrace, cutRawWord, newName, newExt);
	}
	
	public String fullSigString() {
		return this.name + " (" + this.ext + "): " + this.path;
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
		return "one sig " + this.name + " extends " + this.ext + " {} {}";
	}
	
	@Override
	public boolean equals(Object o) {
		if (!(o instanceof AlloyTrace)) {
			return false;
		}
		AlloyTrace other = (AlloyTrace) o;
		if (this.trace == null && other.trace != null) {
			return false;
		}
		if (this.trace != null && other.trace == null) {
			return false;
		}
		// the == covers the case when this.trace and other.trace are both null
		return (this.trace == other.trace) || (this.trace.equals(other.trace));
	}
	
	@Override
	public int hashCode() {
		if (this.trace == null) {
			return 0;
		}
		return this.trace.hashCode();
	}
}
