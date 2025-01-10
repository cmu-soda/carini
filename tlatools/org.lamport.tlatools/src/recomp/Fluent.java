package recomp;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import gov.nasa.jpf.util.json.JSONObject;
import tlc2.Utils;
import tlc2.Utils.Pair;

public class Fluent {
	public final String name;
	public final List<String> paramTypes;
	public final String initially;
	public final Set<Pair<String, List<Integer>>> init;
	public final Set<Pair<String, List<Integer>>> term;
	public final Set<Pair<String, List<Integer>>> mutInit;
	public final Set<Pair<String, List<Integer>>> falsify;
	public final Set<String> initBaseNames;
	public final Set<String> termBaseNames;
	public final Set<String> mutInitBaseNames;
	public final Set<String> falsifyBaseNames;
	
	public Fluent(final String name, final JSONObject fluentInfo) {
		this.name = name;
		this.paramTypes = Utils.toArrayList(fluentInfo.getValue("paramTypes").getArray())
				.stream()
				.map(v -> v.getString())
				.collect(Collectors.toList());
		this.initially = fluentInfo.getValue("initially").getString();
		this.init = Utils.toArrayList(fluentInfo.getValue("init").getArray())
				.stream()
				.map(kv -> {
					final JSONObject actInfo = kv.getObject();
					Utils.assertTrue(actInfo.getValuesKeys().length == 1, "Fluent init act info has multiple keys");
					final String act = actInfo.getValuesKeys()[0];
					final List<Integer> paramMap = Utils.toArrayList(actInfo.getValue(act).getArray())
							.stream()
							.map(v -> v.getDouble().intValue())
							.collect(Collectors.toList());
					return new Pair<>(act, paramMap);
				})
				.collect(Collectors.toSet());
		this.term = Utils.toArrayList(fluentInfo.getValue("term").getArray())
				.stream()
				.map(kv -> {
					final JSONObject actInfo = kv.getObject();
					Utils.assertTrue(actInfo.getValuesKeys().length == 1, "Fluent term act info has multiple keys");
					final String act = actInfo.getValuesKeys()[0];
					final List<Integer> paramMap = Utils.toArrayList(actInfo.getValue(act).getArray())
							.stream()
							.map(v -> v.getDouble().intValue())
							.collect(Collectors.toList());
					return new Pair<>(act, paramMap);
				})
				.collect(Collectors.toSet());
		this.mutInit = Utils.toArrayList(fluentInfo.getValue("mutInit").getArray())
				.stream()
				.map(kv -> {
					final JSONObject actInfo = kv.getObject();
					Utils.assertTrue(actInfo.getValuesKeys().length == 1, "Fluent mutInit act info has multiple keys");
					final String act = actInfo.getValuesKeys()[0];
					final List<Integer> paramMap = Utils.toArrayList(actInfo.getValue(act).getArray())
							.stream()
							.map(v -> v.getDouble().intValue())
							.collect(Collectors.toList());
					return new Pair<>(act, paramMap);
				})
				.collect(Collectors.toSet());
		this.falsify = Utils.toArrayList(fluentInfo.getValue("falsify").getArray())
				.stream()
				.map(kv -> {
					final JSONObject actInfo = kv.getObject();
					Utils.assertTrue(actInfo.getValuesKeys().length == 1, "Fluent falsify act info has multiple keys");
					final String act = actInfo.getValuesKeys()[0];
					final List<Integer> paramMap = Utils.toArrayList(actInfo.getValue(act).getArray())
							.stream()
							.map(v -> v.getDouble().intValue())
							.collect(Collectors.toList());
					return new Pair<>(act, paramMap);
				})
				.collect(Collectors.toSet());
		this.initBaseNames = this.init
				.stream()
				.map(p -> p.first)
				.collect(Collectors.toSet());
		this.termBaseNames = this.term
				.stream()
				.map(p -> p.first)
				.collect(Collectors.toSet());
		this.mutInitBaseNames = this.mutInit
				.stream()
				.map(p -> p.first)
				.collect(Collectors.toSet());
		this.falsifyBaseNames = this.falsify
				.stream()
				.map(p -> p.first)
				.collect(Collectors.toSet());
	}
	
	public String toJson() {
		final String paramTypes = "\"paramTypes\":[" +
				this.paramTypes
					.stream()
					.map(pt -> "\"" + pt + "\"")
					.collect(Collectors.joining(","))
				+ "]";
		final String initially = "\"initially\":\"" + this.initially + "\"";
		
		final String initActs = this.init
				.stream()
				.map(a -> {
					final String act = "\"" + a.first + "\"";
					final String pmapContents = a.second
							.stream()
							.map(p -> Integer.toString(p))
							.collect(Collectors.joining(","));
					return "{" + act + ":[" + pmapContents + "]}";
				})
				.collect(Collectors.joining(","));
		final String termActs = this.term
				.stream()
				.map(a -> {
					final String act = "\"" + a.first + "\"";
					final String pmapContents = a.second
							.stream()
							.map(p -> Integer.toString(p))
							.collect(Collectors.joining(","));
					return "{" + act + ":[" + pmapContents + "]}";
				})
				.collect(Collectors.joining(","));
		final String mutInitActs = this.mutInit
				.stream()
				.map(a -> {
					final String act = "\"" + a.first + "\"";
					final String pmapContents = a.second
							.stream()
							.map(p -> Integer.toString(p))
							.collect(Collectors.joining(","));
					return "{" + act + ":[" + pmapContents + "]}";
				})
				.collect(Collectors.joining(","));
		final String falsifyActs = this.falsify
				.stream()
				.map(a -> {
					final String act = "\"" + a.first + "\"";
					final String pmapContents = a.second
							.stream()
							.map(p -> Integer.toString(p))
							.collect(Collectors.joining(","));
					return "{" + act + ":[" + pmapContents + "]}";
				})
				.collect(Collectors.joining(","));
		
		final String init = "\"init\":[" + initActs + "]";
		final String term = "\"term\":[" + termActs + "]";
		final String mutInit = "\"mutInit\":[" + mutInitActs + "]";
		final String falsify = "\"falsify\":[" + falsifyActs + "]";
		
		return "{" + String.join(",", List.of(paramTypes, initially, init, term, mutInit, falsify)) + "}";
	}
	
	@Override
	public String toString() {
		final String initStr = this.init
			.stream()
			.map(a -> {
				final String act = a.first;
				final String pmapContents = a.second
						.stream()
						.map(i -> Integer.toString(i))
						.collect(Collectors.joining(","));
				final String pmap = "[" + pmapContents + "]";
				return act + ": " + pmap;
			})
			.collect(Collectors.joining("\n          "));
		final String termStr = this.term
				.stream()
				.map(a -> {
					final String act = a.first;
					final String pmapContents = a.second
							.stream()
							.map(i -> Integer.toString(i))
							.collect(Collectors.joining(","));
					final String pmap = "[" + pmapContents + "]";
					return act + ": " + pmap;
				})
				.collect(Collectors.joining("\n          "));
		final String mutInitStr = this.mutInit
				.stream()
				.map(a -> {
					final String act = a.first;
					final String pmapContents = a.second
							.stream()
							.map(i -> Integer.toString(i))
							.collect(Collectors.joining(","));
					final String pmap = "[" + pmapContents + "]";
					return act + ": " + pmap;
				})
				.collect(Collectors.joining("\n             "));
			final String falsifyStr = this.falsify
				.stream()
				.map(a -> {
					final String act = a.first;
					final String pmapContents = a.second
							.stream()
							.map(i -> Integer.toString(i))
							.collect(Collectors.joining(","));
					final String pmap = "[" + pmapContents + "]";
					return act + ": " + pmap;
				})
				.collect(Collectors.joining("\n             "));
		
		return "  " + this.name + ":\n"
				+ "    initially: " + this.initially + "\n"
				+ "    init: " + initStr + "\n"
				+ "    term: " + termStr + "\n"
				+ "    mutInit: " + mutInitStr + "\n"
				+ "    falsify: " + falsifyStr;
	}
}
