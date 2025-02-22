package tlc2;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Scanner;
import java.util.Set;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

public class Utils {
	private static final String QUOTE = "\"";
	private static final String COLON = ":";
	private static final String LSQBRACE = "[";
	private static final String RSQBRACE = "]";
	
	private static final String MAX_NEG_EXAMPLES_ENV_VAR_KEY = "TLA_ROBUST_MAX_NEG_EXAMPLES";
	private static final int DEFAULT_MAX_NEG_EXAMPLES = Integer.MAX_VALUE;
	
	
    public static class Pair<A,B> {
        public A first;
        public B second;
        
        public Pair(A f, B s) {
        	first = f;
        	second = s;
        }
        
        @Override
        public int hashCode() {
        	return first.hashCode() + 5701 * second.hashCode();
        }
        
        @Override
        public boolean equals(Object other) {
        	if (other instanceof Pair<?,?>) {
        		Pair<?,?> p = (Pair<?,?>) other;
        		return this.first.equals(p.first) && this.second.equals(p.second);
        	}
        	return false;
        }
        
        @Override
        public String toString() {
        	return "Pair(" + first.toString() + ", " + second.toString() + ")";
        }
    }
    
    public static <A,B> Set<A> projectFirst(Set<Pair<A,B>> set) {
    	Set<A> proj = new HashSet<A>();
    	for (Pair<A,B> e : set) {
    		proj.add(e.first);
    	}
    	return proj;
    }
    
    
    /* utils over relations */
    
    /**
     * Compute the transitive closure over the given relation. This method mutates the input parameter.
     * @param relation
     */
    public static void transitiveClosure(Set<Pair<String,String>> relation) {
    	boolean reachedClosure = false;
    	while (!reachedClosure) {
    		reachedClosure = true;
    		for (Pair<String,String> e1 : relation) {
        		for (Pair<String,String> e2 : relation) {
        			if (!e1.equals(e2) && e1.second.equals(e2.first)) {
        				// in this case we should have: (e1.first,e2.second) \in relation
        				Pair<String,String> trans = new Utils.Pair<>(e1.first,e2.second);
        				if (!relation.contains(trans)) {
        					relation.add(trans);
        					reachedClosure = false;
        					break;
        				}
        			}
        		}
        		if (!reachedClosure) {
        			break;
        		}
    		}
    		// break to here
    	}
    }
    
    /**
     * Assumes that <relation> has a unique largest element. <relation> can be a partial or total
     * ordering.
     * @param relation
     * @return
     */
    public static String largestElement(final Set<Pair<String,String>> relation) {
    	// if there is a unique largest element, it must occur as the first element in each pair in <relation>
    	final Set<String> elems = relation
    			.stream()
    			.map(e -> e.first)
    			.collect(Collectors.toSet());
    	for (final String cand : elems) {
    		boolean isLargest = true;
    		for (final Pair<String,String> e : relation) {
    			if (!cand.equals(e.first) && cand.equals(e.second)) {
    				// <cand> is smaller than some element in <relation> and hence cannot be the largest
    				isLargest = false;
    				break;
    			}
    		}
    		if (isLargest) {
	    		// at this point, no element is larger than <cand>
	    		return cand;
    		}
    	}
    	
    	// if there is a largest element then we should not reach this line
    	Utils.assertTrue(false, "No largest element detected!");
    	return null;
    }
    
    
    public static int maxNegExamples() {
    	if (System.getenv().containsKey(MAX_NEG_EXAMPLES_ENV_VAR_KEY)) {
    		final String sval = System.getenv().get(MAX_NEG_EXAMPLES_ENV_VAR_KEY);
    		try {
    			return Integer.parseInt(sval);
    		} catch (NumberFormatException e) {
    			// do nothing, just return the default value
    		}
    	}
    	return DEFAULT_MAX_NEG_EXAMPLES;
    }

	
	/* Because assert() doesn't seem to work */
	
	public static void assertTrue(final boolean condition, final String msg) {
		if (!condition) {
			System.err.println("\n\n!!! assertTrue failed with message: " + msg + "\n\n");
			Thread.dumpStack();
			System.exit(1);
		}
	}
	
	public static void assertNull(final Object obj, final String msg) {
		if (obj != null) {
			System.err.println("\n\n!!! assertNull failed with message: " + msg + "\n\n");
			Thread.dumpStack();
			System.exit(1);
		}
	}
	
	public static void assertNotNull(final Object obj, final String msg) {
		if (obj == null) {
			System.err.println("\n\n!!! assertNotNull failed with message: " + msg + "\n\n");
			Thread.dumpStack();
			System.exit(1);
		}
	}
	
	
	public static String firstLetterToUpperCase(final String str) {
		  char c[] = str.toCharArray();
		  c[0] = Character.toUpperCase(c[0]);
		  return new String(c);
	}
	
	public static String firstLetterToLowerCase(final String str) {
		  char c[] = str.toCharArray();
		  c[0] = Character.toLowerCase(c[0]);
		  return new String(c);
	}
	
	
    @SafeVarargs
	public static <T> Set<T> union(Set<T>... sets) {
    	Set<T> un = new HashSet<T>();
    	for (final Set<T> s : sets) {
    		un.addAll(s);
    	}
    	return un;
    }
    
    public static <T> Set<T> intersection(Set<T> s1, Set<T> s2) {
    	Set<T> inters = new HashSet<T>();
    	inters.addAll(s1);
    	inters.retainAll(s2);
    	return inters;
    }
    
    public static <T> Set<T> setMinus(Set<T> s1, Set<T> s2) {
    	Set<T> setmin = new HashSet<T>();
    	setmin.addAll(s1);
    	setmin.removeAll(s2);
    	return setmin;
    }
    
    public static <T> T singletonGetElement(Set<T> set) {
    	assert(set.size() == 1);
    	T elem = null;
    	for (T e : set) {
    		elem = e;
    	}
    	return elem;
    }
    
    public static <T> T chooseOne(Set<T> s) {
    	Utils.assertTrue(!s.isEmpty(), "Called chooseOne() on an empty set");
    	return s.iterator().next();
    }
    
    public static <T> Set<T> setOf(T... elems) {
    	Set<T> s = new HashSet<>();
    	for (T e : elems) {
        	s.add(e);
    	}
    	return s;
    }
    
    // this method is completely untested
    public static <T> Set<Set<T>> powerSet(Set<T> set) {
    	if (set.isEmpty()) {
    		return new HashSet<Set<T>>();
    	}
    	T e = chooseOne(set);
    	Set<T> rest = setMinus(set, setOf(e));
    	Set<Set<T>> restPowerSetWithE = powerSet(rest);
    	for (Set<T> s : restPowerSetWithE) {
    		s.add(e);
    	}
    	return union(restPowerSetWithE, powerSet(rest));
    }
    
    public static <T> Set<List<T>> cartesianProductOfTraces(List<Set<T>> sets) {
    	Set<List<T>> prod = new HashSet<>();
    	prod.add(new ArrayList<>());
		for (Set<T> set : sets) {
			Set<List<T>> newProd = new HashSet<>();
			for (T elem : set) {
				for (List<T> trace : prod) {
					List<T> newTrace = new ArrayList<>(trace);
					newTrace.add(elem);
					newProd.add(newTrace);
				}
			}
			prod = newProd;
		}
		return prod;
    }
	
    
    public static ArrayList<Pair<String,String>> extractKeyValuePairsFromState(String tlaState) {
    	ArrayList<Pair<String,String>> kvPairs = new ArrayList<>();
    	String[] conjuncts = tlaState.split(Pattern.quote("/\\"));
    	for (int i = 0; i < conjuncts.length; ++i) {
    		final String tlaConjunct = conjuncts[i];
    		final Pair<String,String> kvPair = extractKeyValuePairFromAssignment(tlaConjunct);
    		kvPairs.add(kvPair);
    	}
    	return kvPairs;
    }
    
    public static Pair<String, String> extractKeyValuePairFromAssignment(String assg) {
    	String[] kvp = assg.split("=");
		assert(kvp.length == 2);
		final String key = kvp[0].trim();
		final String val = kvp[1].trim();
		if (val.equals("null")) {
			System.err.println("Warning: found null valued state var!");
		}
		return new Pair<>(key,val);
    }
    
    public static String normalizeStateString(String s) {
    	final String[] rawConjuncts = s.replace("\n", "").split(Pattern.quote("/\\"));
    	ArrayList<String> clist = new ArrayList<>();
    	for (int i = 0; i < rawConjuncts.length; ++i) {
    		final String c = rawConjuncts[i].trim();
    		if (!c.isEmpty()) {
    			clist.add(c);
    		}
    	}
    	final String[] conjuncts = toStringArray(clist);
		Arrays.sort(conjuncts);
		return String.join(" /\\ ", conjuncts);
	}
	
	public static String instanceWithList(ArrayList<String> vars) {
    	ArrayList<String> varArrowList = new ArrayList<String>();
    	for (String var : vars) {
    		final String arrow = var + " <- " + var;
    		varArrowList.add(arrow);
    	}
    	return String.join(", ", varArrowList);
    }
    
    public static <T> List<T> listOf(T elem) {
    	List<T> l = new ArrayList<>();
    	l.add(elem);
    	return l;
    }
    
    public static <T> List<T> append(List<T> l1, List<T> l2) {
    	List<T> l = new ArrayList<>(l1);
    	l.addAll(l2);
    	return l;
    }

    public static <T> ArrayList<T> toArrayList(Set<T> src) {
    	ArrayList<T> dst = new ArrayList<T>();
    	for (T s : src) {
    		dst.add(s);
    	}
    	return dst;
    }

    public static <T> ArrayList<T> toArrayList(T[] src) {
    	ArrayList<T> dst = new ArrayList<T>();
    	for (int i = 0; i < src.length; ++i) {
    		dst.add(src[i]);
    	}
    	return dst;
    }

    public static <T> Set<T> toSet(T[] src) {
    	Set<T> dst = new HashSet<T>();
    	for (int i = 0; i < src.length; ++i) {
    		dst.add(src[i]);
    	}
    	return dst;
    }
    
    public static <T> List<String> toStringList(Collection<T> src) {
    	List<String> dst = new ArrayList<>();
    	for (T e : src) {
    		dst.add(e.toString());
    	}
    	return dst;
    }
    
    public static <T> String[] toStringArray(Collection<T> src) {
    	String[] dst = new String[src.size()];
    	int i = 0;
    	for (T e : src) {
    		dst[i++] = e.toString();
    	}
    	return dst;
    }
    
    public static ArrayList<String> filterArrayBlackList(String filter, String[] arr) {
    	ArrayList<String> filtered = new ArrayList<String>();
    	for (int i = 0; i < arr.length; ++i) {
    		String e = arr[i];
    		if (!filter.equals(e)) {
    			filtered.add(e);
    		}
    	}
    	return filtered;
    }
    
    public static ArrayList<String> filterArrayWhiteList(List<String> filter, String[] arr) {
    	ArrayList<String> filtered = new ArrayList<String>();
    	for (int i = 0; i < arr.length; ++i) {
    		String e = arr[i];
    		if (filter.contains(e)) {
    			filtered.add(e);
    		}
    	}
    	return filtered;
    }
    
    public static int findFirstLineOfSpec(ArrayList<String> lines) {
    	for (int i = 0; i < lines.size(); ++i) {
    		String line = lines.get(i);
    		if (line.length() >= 3 && line.substring(0,3).equals("---")) {
    			return i;
    		}
    	}
    	throw new RuntimeException("Unable to find the last line in the TLA+ spec!");
    }
    
    public static int findLastLineOfSpec(ArrayList<String> lines) {
    	for (int i = lines.size()-1; i >= 0; --i) {
    		String line = lines.get(i);
    		if (line.length() >= 3 && line.substring(0,3).equals("===")) {
    			return i;
    		}
    	}
    	throw new RuntimeException("Unable to find the last line in the TLA+ spec!");
    }
    
    public static <K,V> Map<K,V> mergeMapsOrError(Map<K,V> map1, Map<K,V> map2) {
    	// make sure the two maps agree on the value of any mutual keys
    	final Set<K> mutualKeys = intersection(map1.keySet(), map2.keySet());
    	for (final K key : mutualKeys) {
    		assertTrue(map1.get(key).equals(map2.get(key)), "Attempting to merge maps with different values for key: " + key);
    	}
    	// merge the maps
    	HashMap<K,V> merged = new HashMap<>(map1);
    	for (final Map.Entry<K,V> entry : merged.entrySet()) {
    		merged.put(entry.getKey(), entry.getValue());
    	}
    	return merged;
    }
    
    public static void printStringArr(ArrayList<String> arr) {
    	for (String s : arr) {
    		System.out.println(s);
    	}
    }
    
    public static void printVerbose(boolean verbose, final String msg) {
    	if (verbose) {
    		System.out.println(msg);
    	}
    }
    
    public static boolean isIntegerString(final String str) {
    	try {
    		Integer.parseInt(str);
    		return true;
    	} catch (NumberFormatException e) {}
    	return false;
    }
    
    // thanks https://stackoverflow.com/questions/2406121/how-do-i-escape-a-string-in-java
    public static String stringEscape(String s){
	  return s.replace("\\", "\\\\")
	          .replace("\t", "\\t")
	          .replace("\b", "\\b")
	          .replace("\n", "\\n")
	          .replace("\r", "\\r")
	          .replace("\f", "\\f")
	          .replace("\'", "\\'")
	          .replace("\"", "\\\"");
	}
    
    public static String extractSyntaxFromSource(final String tla, final String loc) {
    	String[] parts = loc.replaceAll(",", "").split(" ");
    	int startLine = -1;
    	int startCol = -1;
    	int endLine = -1;
    	int endCol = -1;
    	for (int i = 0; i < parts.length-1; ++i) {
    		final String part = parts[i];
			final String strLineOrColNum = parts[i+1];
    		if (part.equals("line") && startLine < 0) {
    			startLine = Integer.parseInt(strLineOrColNum) - 1;
    		}
    		else if (part.equals("line") && startLine >= 0) {
    			endLine = Integer.parseInt(strLineOrColNum) - 1;
    		}
    		else if (part.equals("col") && startCol < 0) {
    			startCol = Integer.parseInt(strLineOrColNum) - 1;
    		}
    		else if (part.equals("col") && startCol >= 0) {
    			endCol = Integer.parseInt(strLineOrColNum);
    		}
    	}
    	assert(startLine >= 0);
    	assert(startCol >= 0);
    	assert(endLine >= 0);
    	assert(endCol >= 0);
    	assert(startLine <= endLine);

    	ArrayList<String> tlaSource = fileContents(tla);
    	// single line extraction
    	if (startLine == endLine) {
    		final String line = tlaSource.get(startLine);
    		final String syntax = line.substring(startCol, endCol);
    		return syntax;
    	}
    	// multi-line extraction
    	else {
        	StringBuilder builder = new StringBuilder();
        	for (int i = startLine; i <= endLine; ++i) {
        		final String line = tlaSource.get(i);
        		if (i == startLine) {
        			builder.append(line.substring(startCol));
        		}
        		else if (i == endLine) {
        			builder.append(" ").append(line.substring(0, endCol));
        		}
        		else {
        			builder.append(" ").append(line);
        		}
        	}
        	return builder.toString();
    	}
    }
    
    public static void writeFile(String file, String contents) {
    	try {
    		FileOutputStream writer = new FileOutputStream(file);
    	    writer.write(contents.getBytes(), 0, contents.length());
    	    writer.close();
    	}
    	catch (IOException e) {
    		throw new RuntimeException("Failed to write to file: " + file + "!");
    	}
    }
    
    public static void copyFile(String src, String dst) {
    	try {
  	      Scanner scan = new Scanner(new File(src));
	  	  FileOutputStream writer = new FileOutputStream(dst);
  	      while (scan.hasNextLine()) {
  	        final String line = scan.nextLine() + "\n";
		    writer.write(line.getBytes(), 0, line.length());
  	      }
  	      scan.close();
		  writer.close();
  	    } catch (IOException e) {
  	      e.printStackTrace();
  	    }
    }
    
    public static ArrayList<String> fileContents(String loc) {
    	ArrayList<String> lines = new ArrayList<String>();
    	try {
	      Scanner scan = new Scanner(new File(loc));
	      while (scan.hasNextLine()) {
	        lines.add(scan.nextLine());
	      }
	      scan.close();
	    } catch (FileNotFoundException e) {
	      System.out.println("The file " + loc + " does not exist!");
	      e.printStackTrace();
	    }
    	return lines;
    }
    
    public static void deleteFile(String file) {
		new File(file).delete();
    }
	
    public static String asJson(Map<String,String> jsonStrs, Map<String,List<String>> jsonLists) {
    	final String strs = asJsonStrs(jsonStrs);
    	final String lists = asJsonLists(jsonLists);
    	if (strs.isEmpty() && lists.isEmpty()) {
    		return "{}";
    	}
    	else if (strs.isEmpty()) {
        	return "{" + lists + "}";
    	}
    	else if (lists.isEmpty()) {
        	return "{" + strs + "}";
    	}
    	else {
        	return "{" + strs + "," + lists + "}";
    	}
    }
	
    private static String asJsonStrs(Map<String,String> output) {
    	List<String> fields = new ArrayList<>();
    	for (String key : output.keySet()) {
    		final String value = output.get(key);
        	StringBuilder builder = new StringBuilder();
    		builder.append(QUOTE).append(key).append(QUOTE).append(COLON)
    			.append(QUOTE).append(value).append(QUOTE);
    		fields.add(builder.toString());
    	}
    	final String fieldsStr = String.join(",", fields);
    	return fieldsStr;
    }
    
    private static String asJsonLists(Map<String,List<String>> output) {
    	List<String> fields = new ArrayList<>();
    	for (String key : output.keySet()) {
    		final List<String> value = output.get(key);
    		final String flatValue = "\"" + String.join("\",\"", value) + "\"";
        	StringBuilder builder = new StringBuilder();
    		builder.append(QUOTE).append(key).append(QUOTE).append(COLON)
    			.append(LSQBRACE).append(flatValue).append(RSQBRACE);
    		fields.add(builder.toString());
    	}
    	final String fieldsStr = String.join(",", fields);
    	return fieldsStr;
    }
}
