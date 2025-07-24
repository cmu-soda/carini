package recomp;

import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;

import gov.nasa.jpf.util.json.JSONObject;
import tlc2.Utils;

public class FlAction {
	public final String baseName;
	public final int priority;
	public final List<Integer> paramMap;
	public final String value;

	public FlAction(final JSONObject flActInfo) {
		this.baseName = flActInfo.getValue("baseName").getString();
		this.priority = (int) flActInfo.getValue("priority").getDouble().doubleValue();
		this.paramMap = Utils.toArrayList(flActInfo.getValue("paramMap").getArray())
				.stream()
				.map(v -> v.getDouble().intValue())
				.collect(Collectors.toList());
		this.value = flActInfo.getValue("value").getString();
	}
	
	public String toJson() {
		final String baseNameStr = "\"baseName\":\"" + this.baseName + "\"";
		final String priorityStr = "\"priority\":" + this.priority;
		final String paramMapStr = "\"paramMap\":" + this.paramMap;
		final String valueStr = "\"value\":\"" + this.value + "\"";
		
		return "{" + String.join(",", List.of(baseNameStr, priorityStr, paramMapStr, valueStr)) + "}";
	}
	
	@Override
	public String toString() {
		final String pri = this.priority == 0 ? "" : " (priority " + this.priority + ")";
		return this.baseName + this.paramMap + " = " + this.value + pri;
	}
	
	@Override
	public int hashCode() {
		return Objects.hash(this.baseName, this.priority, this.paramMap, this.value);
	}
	
	@Override
	public boolean equals(Object o) {
		if (!(o instanceof FlAction)) {
			return false;
		}
		final FlAction other = (FlAction)o;
		return this.baseName.equals(other.baseName) && this.priority == other.priority &&
				this.paramMap.equals(other.paramMap) && this.value.equals(other.value);
	}
}
