package recomp;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import gov.nasa.jpf.util.json.JSONLexer;
import gov.nasa.jpf.util.json.JSONObject;
import gov.nasa.jpf.util.json.JSONParser;

public class Formula {
	private final String formula;
	private final List<String> conjuncts;
	private final boolean isUNSAT;
	private final Map<String, Fluent> fluents;
	
	public static Formula UNSAT() {
		return new Formula("UNSAT", true);
	}
	
	private static Formula TRUE() {
		return new Formula("TRUE", false);
	}
	
	public static Formula conjunction(final List<Formula> formulas) {
		if (formulas.isEmpty()) {
			return TRUE();
		}
		
		final List<String> conjuncts = formulas
				.stream()
				.map(f -> f.getFormula())
				.filter(f -> !f.equals("TRUE"))
				.collect(Collectors.toList());
		if (conjuncts.isEmpty()) {
			return TRUE();
		}
		
		final String formula = prettyConjuncts(conjuncts);
		final boolean isUNSAT = conjuncts
				.stream()
				.allMatch(f -> !f.contains("UNSAT"));
		
		Map<String,Fluent> fluents = new HashMap<>();
		for (final Formula form : formulas) {
			fluents.putAll(form.fluents);
		}
		
		return new Formula(formula, conjuncts, isUNSAT, fluents);
	}
	
	private static String prettyConjuncts(final List<String> conjuncts) {
		if (conjuncts.isEmpty()) {
			return "TRUE";
		}
		final String delim = "\n/\\ ";
		return "/\\ " + String.join(delim, conjuncts);
	}
	
	
	public Formula(final String json) {
		try {
			final JSONObject info = new JSONParser(new JSONLexer(json)).parse();
			
			this.formula = info.getValue("formula").getString();
			this.conjuncts = new ArrayList<>();
			this.conjuncts.add(this.formula);
			this.isUNSAT = this.formula.contains("UNSAT");
			this.fluents = new HashMap<>();
			
			if (!this.isUNSAT) {
				final JSONObject fluents = info.getValue("fluents").getObject();
				for (final String fluent : fluents.getValuesKeys()) {
					final JSONObject fluentInfo = fluents.getValue(fluent).getObject();
					this.fluents.put(fluent, new Fluent(fluent, fluentInfo));
				}
			}
		}
		catch (gov.nasa.jpf.JPFException e) {
			System.err.println("The following JSON is malformed:");
			System.err.println(json);
			//System.err.println("The JSON output came from worker: " + workerId);
			throw e;
		}
	}
	
	private Formula(final String formula, boolean isUNSAT) {
		this.formula = formula;
		this.conjuncts = new ArrayList<>();
		this.conjuncts.add(formula);
		this.isUNSAT = isUNSAT;
		this.fluents = new HashMap<>();
	}
	
	private Formula(String formula, List<String> conjuncts, boolean isUNSAT, Map<String,Fluent> fluents) {
		this.formula = formula;
		this.conjuncts = conjuncts;
		this.isUNSAT = isUNSAT;
		this.fluents = fluents;
	}
	
	
	public String getFormula() {
		return this.formula;
	}
	
	public boolean isUNSAT() {
		return this.isUNSAT;
	}
	
	public Collection<Fluent> getFluents() {
		return this.fluents.values();
	}
	
	public Set<String> getFluentVars() {
		return this.fluents.keySet();
	}
	
	public int getNumFluents() {
		return getFluentVars().size();
	}
	
	public boolean containsQuantifiedType(final String qtype) {
		return this.formula.contains("\\in " + qtype + " :");
	}
	
	/**
	 * Determines the number of fluents by the number encoded into each fluent
	 * name. This effectively tells us how many fluents have been created in the
	 * past. This method is useful to get the number of previous fluents from
	 * intermediate properties; we can increment this number so the next fluent
	 * doesn't clash with any previous one. 
	 * @return
	 */
	public int getPastNumFluents() {
		return this.fluents.keySet()
				.stream()
				.map(f -> f.replace("Fluent", ""))
				.map(f -> f.replaceAll("_.*$", ""))
				.mapToInt(f -> Integer.parseInt(f))
				.max()
				.getAsInt();
	}
	
	public String toJson() {
		final String fluentsObjContents = this.fluents.keySet()
				.stream()
				.map(f -> "\"" + f + "\":" + this.fluents.get(f).toJson())
				.collect(Collectors.joining(","));
		final String fluentsObj = "{" + fluentsObjContents + "}";
		final String escapedFormula = this.formula
				.replace("\\", "\\\\")  // escape backslashes
				.replace("\n", "\\n"); // escape newlines
		
		return "{\"formula\":\"" + escapedFormula + "\",\"fluents\":" + fluentsObj + "}";
	}
	
	@Override
	public String toString() {
		return this.formula + "\n" + this.fluents.values()
				.stream()
				.map(fl -> fl.toString())
				.collect(Collectors.joining("\n"));
	}
}
