package recomp;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import tlc2.Utils;

public class TraceTree {
	private int globalId = 2;
	private Node root = new Node(null, null, true, 1);

	public void addPosTrace(List<String> trace) {
		addTrace(trace, trace.size());
	}
	
	public void addNegTrace(List<String> trace, int startNegIdx) {
		Utils.assertTrue(0 <= startNegIdx && startNegIdx < trace.size(),
				"Invalid startNegIdx! It is: " + startNegIdx + ", trace.size(): " + trace.size());
		addTrace(trace, startNegIdx);
	}

	public void addTrace(List<String> trace, int startNegIdx) {
		Node curNode = root;
		int idx = 0;
		for (final String act : trace) {
			// cycle through the tree while we find states that already exist
			if (curNode.nextNodes.containsKey(act)) {
				curNode = curNode.nextNodes.get(act);
			}
			// found a state that does not already exist in the tree
			else {
				boolean isPosState = idx < startNegIdx;
				Node newNextNode = new Node(curNode, act, isPosState, globalId++);
				curNode.nextNodes.put(act, newNextNode);
				curNode = newNextNode;
			}
			++idx;
		}
	}
	
	private void treeVisitor(Node node, StringBuilder builder) {
		builder.append(node.toString()).append("\n\n");
		for (Node next : node.nextNodes.values()) {
			treeVisitor(next, builder);
		}
	}
	
	@Override
	public String toString() {
		StringBuilder builder = new StringBuilder();
		treeVisitor(root, builder);
		return builder.toString();
	}
	
	/**
	 * The inner tree node class
	 */
	private class Node {
		Map<String, Node> nextNodes;
		Node prevNode;
		String act;
		boolean posState;
		int id;
		
		public Node(Node pn, String a, boolean ps, int i) {
			nextNodes = new HashMap<>(); // next nodes will be updated dynamically
			prevNode = pn;
			act = a;
			posState = ps;
			id = i;
		}
		
		public String polarity() {
			return posState ? "PosState" : "NegState";
		}
		
		public String name() {
			return polarity() + id;
		}
		
		@Override
		public String toString() {
			final String prevStateStr = prevNode == null ? "no prevState" : "prevState = " + prevNode.name();
			final String prevActStr = act == null ? "no act" : "act = " + act;
			return "one sig " + name() + " extends " + polarity() + " {} {\n"
					+ "    " + prevStateStr + "\n"
					+ "    " + prevActStr + "\n"
					+ "}";
		}
	}
}
