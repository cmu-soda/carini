package recomp;

import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;

import gov.nasa.jpf.util.json.JSONObject;
import tlc2.Utils;

public class FlAction {
	public final String baseName;
	public final List<Integer> paramMap;
	public final String value;
	public final String isMutexFlStr;
	public final boolean isMutexFl;

	public FlAction(final JSONObject flActInfo) {
		this.baseName = flActInfo.getValue("baseName").getString();
		this.paramMap = Utils.toArrayList(flActInfo.getValue("paramMap").getArray())
				.stream()
				.map(v -> v.getDouble().intValue())
				.collect(Collectors.toList());
		this.value = flActInfo.getValue("value").getString();
		
		this.isMutexFlStr = flActInfo.getValue("mutexFl").getString();
		this.isMutexFl = this.isMutexFlStr.contains("TRUE");
	}
	
	public String toJson() {
		final String baseNameStr = "\"baseName\":\"" + this.baseName + "\"";
		final String paramMapStr = "\"paramMap\":" + this.paramMap;
		final String valueStr = "\"value\":\"" + this.value + "\"";
		final String mutexFlStr = "\"mutexFl\":\"" + this.isMutexFlStr + "\"";
		
		return "{" + String.join(",", List.of(baseNameStr, paramMapStr, valueStr, mutexFlStr)) + "}";
	}
	
	@Override
	public String toString() {
		final String mut = this.isMutexFl ? " (mutexFl)" : "";
		return this.baseName + this.paramMap + " = " + this.value + mut;
	}
	
	@Override
	public int hashCode() {
		return Objects.hash(this.baseName, this.paramMap, this.value, this.isMutexFl);
	}
	
	@Override
	public boolean equals(Object o) {
		if (!(o instanceof FlAction)) {
			return false;
		}
		final FlAction other = (FlAction)o;
		return this.baseName.equals(other.baseName) && this.paramMap.equals(other.paramMap) &&
				this.value.equals(other.value) && this.isMutexFl == other.isMutexFl;
	}
}
