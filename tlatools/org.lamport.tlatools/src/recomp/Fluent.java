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
	public final Set<FlAction> flActions;
	
	public Fluent(final String name, final JSONObject fluentInfo) {
		this.name = name;
		this.paramTypes = Utils.toArrayList(fluentInfo.getValue("paramTypes").getArray())
				.stream()
				.map(v -> v.getString())
				.collect(Collectors.toList());
		this.initially = fluentInfo.getValue("initially").getString();
		this.flActions = Utils.toArrayList(fluentInfo.getValue("actionFls").getArray())
				.stream()
				.map(a -> new FlAction(a.getObject()))
				.collect(Collectors.toSet());
	}
	
	public boolean hasActionBaseName(final String baseName) {
		return this.flActions
				.stream()
				.anyMatch(a -> a.baseName.equals(baseName));
	}
	
	public String toJson() {
		final String paramTypes = "\"paramTypes\":[" +
				this.paramTypes
					.stream()
					.map(pt -> "\"" + pt + "\"")
					.collect(Collectors.joining(","))
				+ "]";
		final String initially = "\"initially\":\"" + this.initially + "\"";
		
		final String actionFlsContent = this.flActions
				.stream()
				.map(a -> a.toJson())
				.collect(Collectors.joining(","));
		final String actionFls = "\"actionFls\":[" + actionFlsContent + "]";
		
		return "{" + String.join(",", List.of(paramTypes, initially, actionFls)) + "}";
	}
	
	@Override
	public String toString() {
		final String flActs = this.flActions
				.stream()
				.map(a -> a.toString())
				.collect(Collectors.joining("\n      "));
		
		return "  " + this.name + this.paramTypes + "\n"
				+ "    initially: " + this.initially + "\n"
				+ "    flActions:\n"
				+ "      " + flActs;
	}
}
