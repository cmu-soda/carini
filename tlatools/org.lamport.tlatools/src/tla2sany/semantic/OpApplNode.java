// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tla2sany.semantic;

// last modified on Wed  4 March 2009 at 18:58:31 PST by lamport

/***************************************************************************
* Modified on 4 Jul 2007 to change the introduced bound symbols from       *
* OpDeclNodes to FormalParamNodes.                                         *
*                                                                          *
* Note: Level checking uses the fact that the only TLA+ operators that     *
* introduce bound symbols are built-ins, and that the only ones that       *
* introduce bound symbols with non-constant level are \AA and \EE, which   *
* always produce a node of level TemporalLevel.  Hence the levels of       *
* the bound symbols are irrelevant in computing the node's level.          *
***************************************************************************/

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import tla2sany.explorer.ExploreNode;
import tla2sany.explorer.ExplorerVisitor;
import tla2sany.parser.SyntaxTreeNode;
import tla2sany.st.TreeNode;
import tla2sany.utilities.Strings;
import tla2sany.xml.SymbolContext;
import tlc2.Utils;
import tlc2.tool.BuiltInOPs;
import tlc2.value.ITupleValue;
import tlc2.value.IValue;
import tlc2.value.Values;
import util.UniqueString;

/**
 * OpApplNodes represent all kinds of operator applications in TLA+,
 * including the application of builtin
 * ors and user-defined
 * operators, operators with a variable number of arguments or a fixed
 * number (including, of course, 0), and including quantifiers and
 * choose, which involve bound variables with or without bounding sets.
 *
 * We distinguish three different uses of OpApplNode:
 *  o Basic case: getOperator, getArgs, setArgs
 *  o unbounded parameters: getOperator, getArgs, setArgs,
 *                          getUnbdedQuantSymbols, isUnbdedQuantATuple
 *  o messy kind: getOperator, getArgs, setArgs, getBdedQuantSymbolLists,
 *                isBdedQuantATuple, getBdedQuantBounds
 */
public class OpApplNode extends ExprNode implements ExploreNode {
	
  private boolean isSetMalformed = false;

  protected SymbolNode        operator;
     // operator being applied to the operands
  protected ExprOrOpArgNode[] operands;
     // the operands. For an op with no operands
     //   this is a zero-length array


//  protected boolean           isATuple;
     // indicates whether bound vars are in form of a tuple,
     //   e.g. surrounded by << >>
     /**********************************************************************
     * Field eliminated by LL on 3 Aug 2007.                               *
     *                                                                     *
     * It apparently served only to distinguish "CHOOSE x " from "CHOOSE   *
     * <<x>>".  It should also have distinguished "\A x \in S" from "\A    *
     * <<x>> \in S", but it didn't--which looked like a bug.  However,     *
     * the field seems to be useless because the tupleOrs field            *
     * apparently contains the correct information.  Neither the parser    *
     * nor tlc uses the public method that returns the field's value.      *
     **********************************************************************/

  protected FormalParamNode[]      unboundedBoundSymbols;
     // bound symbols introduced without restricted range
  protected FormalParamNode[][]    boundedBoundSymbols;
     // bound symbols introduced with a restricted range
  protected ExprNode[]        ranges;
     // ranges of bounded bound symbols
     /**********************************************************************
     * I believe that this is never null.  It is set to an array of        *
     * length 0 by all but one of the constructors, which sets it equal    *
     * to an argument.  That constructor is called in several places       *
     * within semantic/Generator.java, I believe always with a non-null    *
     * argument.                                                           *
     *                                                                     *
     * I don't know if ranges[i] can ever be null.  I suspect not, since   *
     * some places it's dereferenced without first checking for null.      *
     * However, there is one place in the code where it is checked to see  *
     * if it equals null.                                                  *
     **********************************************************************/
  protected boolean[]         tupleOrs;
     // true if bound variable is in a tuple
     // T.L. it is not clear to me if this array ranges over either of the
     // sets or over both of them. There can be a mixed set of bound variables.

  public SymbolNode subExpressionOf = null ;
    /***********************************************************************
    * For an expression that is constructed as a subexpression of a        *
    * UserDefinedOpNode or ThmOrAssumpDefNode, this field equals that      *
    * node.                                                                *
    ***********************************************************************/

/***************************************************************************
* For now, the boundSymbolLevel field is not needed.  To see why it might  *
* be needed, search for the comment beginning:                             *
*                                                                          *
*    Because of the change of bound identifiers from OpDeclNodes           *
***************************************************************************/
//  protected int boundSymbolLevel = ConstantLevel;
    /***********************************************************************
    * The bounded symbols are now represented as FormalParamNode rather    *
    * than as OpDeclNodes.  Hence, the objects do not indicate the level   *
    * of the bounded symbols.  This field is the level of all the bounded  *
    * symbols, which is ConstantLevel except if the operator is a          *
    * temporal existential or universal quantifier (\EE or \AA).           *
    ***********************************************************************/

  /**  constructor 1
   * Used only for creating "null" OpApplNode, nullOAN in Generator class.
   */
  public OpApplNode(SymbolNode sn) {
    super(OpApplKind, SyntaxTreeNode.nullSTN);
      /*********************************************************************
      * The original implementation had an argument -1 instead of          *
      * OpApplKind.  I don't understand this, since a main purpose of      *
      * creating nullOAN is to allow processing to continue after an       *
      * error is discovered.  This causes code that checks for an          *
      * unexpected node kind to bomb.  Apparently, the SANY1 code didn't   *
      * check for such things.                                             *
      *********************************************************************/
    this.operator = sn;
    this.operands = new ExprNode[0];
    this.unboundedBoundSymbols = null;
//    this.isATuple = false;
    this.boundedBoundSymbols = null;
    this.ranges = new ExprNode[0];
    this.tupleOrs = null;
  }

  /** constructor 2
   * Constructor for base case; used in SubstInNode and many cases in
   * Generator.
   */
  public OpApplNode(SymbolNode op, ExprOrOpArgNode[] oprands, TreeNode stn,
                    ModuleNode mn) throws AbortException {
    super(OpApplKind, stn);
    this.operator = op;
    this.operands = oprands;
    this.unboundedBoundSymbols = null;
//    this.isATuple = false;
    this.boundedBoundSymbols= null;
    this.tupleOrs = null;
    this.ranges = new ExprNode[0];

    // Call the match method for the operator in this op application,
    // with this OpApplNode as argument
    op.match( this, mn );
  }

  /* constructor 3
   * Constructor for builtins --- matching is very specific in this case.
   * This is also used for the "@" construct, which somehow gets treated
   * as an OpApplNode for now
   */
  public OpApplNode(UniqueString us, ExprOrOpArgNode[] ops, TreeNode stn,
                    ModuleNode mn) {
    super(OpApplKind, stn);
    this.operands = ops;
    this.unboundedBoundSymbols = null;
//    this.isATuple = false;
    this.boundedBoundSymbols= null;
    this.tupleOrs = null;
    this.ranges = new ExprNode[0];
    this.operator = Context.getGlobalContext().getSymbol(us);
    // operator.match( this, mn );
  }

  /** constructor 4
   * Constructor used in the case of unbounded quantifiers, and the
   * first arg, "us", indicates which quantifier it is.  constructor
   * for unbounded builtins --- matching is very syntax-specific, and
   * we skip it.
   */
  /*************************************************************************
  * Argument for setting isATuple eliminated 3 Aug 2007.                   *
  *************************************************************************/
  public OpApplNode(UniqueString us, ExprOrOpArgNode[] ops,
                    FormalParamNode[] odns,
                    TreeNode stn, ModuleNode mn) {
    super(OpApplKind, stn);
    this.operands = ops;
    this.unboundedBoundSymbols = odns;
//    this.isATuple = t;
    this.boundedBoundSymbols= null;
    this.tupleOrs = null;
    this.ranges = new ExprNode[0];
    this.operator = Context.getGlobalContext().getSymbol(us);
    // operator.match( this, mn );
  }


  /** constructor 5
   * constructor for builtins & bounded quantifiers, including fcn defs--
   * matching is very syntax-specific in this case and we skip it.
   */
  public OpApplNode(UniqueString us, FormalParamNode[] funcName,
                    ExprOrOpArgNode[] ops, FormalParamNode[][] pars,
                    boolean[] isT, ExprNode[] rs, TreeNode stn,
                    ModuleNode mn) {
    super(OpApplKind, stn);
    this.operands = ops;
    this.unboundedBoundSymbols = funcName;
      // Will be null except for function defs.
      // In that case it will be non-null initially
      // and will be changed to null if the function
      // turns out to be non-recursive.
//    this.isATuple = false;
    this.boundedBoundSymbols= pars;
    this.tupleOrs = isT;
    this.ranges = rs;
    this.operator = Context.getGlobalContext().getSymbol(us);
     // operator.match( this, mn );
  }
  
  @Override
  protected void actionParamTypes(final Set<String> allActions, Map<String,String> env, Map<String, List<String>> apt) {
	  final SymbolNode opNode = this.getOperator();
	  final String opKey = opNode.getName().toString();
	  
	  // if we find a quantifier, add the parameter and its type to the environment
	  if (isBoundedQuant(opKey)) {
		  for (int i = 0; i < this.ranges.length; ++i) {
			  final FormalParamNode[] params = this.boundedBoundSymbols[i];
			  final ExprNode paramType = this.ranges[i];
			  for (final FormalParamNode param : params) {
				  final String key = param.getName().toString();
				  final String val = paramType.toTLA(false);
				  env.put(key, val);
			  }
		  }
	  }
	  // if we're in an action node then map the action to its param types
	  else if (allActions.contains(opKey)) {
		  final String actionName = opKey;
		  if (!apt.containsKey(actionName)) {
			  apt.put(actionName, new ArrayList<>());
		  }
		  
		  for (final ExprOrOpArgNode param : this.operands) {
			  final String paramEnvKey = param.toTLA(false);
			  Utils.assertTrue(env.containsKey(paramEnvKey), "Found action with an unbound parameter!");
			  final String paramType = env.get(paramEnvKey);
			  apt.get(actionName).add(paramType);
		  }
	  }
	  
	  for (SemanticNode child : getChildren()) {
		  child.actionParamTypes(allActions, env, apt);
	  }
  }
  
  @Override
  public Map<String,String> collectTypesFromTypeOK() {
	  final SymbolNode opNode = this.getOperator();
	  final String opKey = opNode.getName().toString();
	  
	  Utils.assertTrue(!opKey.equals("\\subseteq"), "Must use \\in instead of \\subseteq for this heuristic!");
	  
	  // found the type definition
	  if (opKey.equals("\\in")) {
		  Utils.assertTrue(getChildren().length == 2, "\\in op should only be applied to two args!");
		  final String var = getChildren()[0].toTLA(false);
		  final String type = getChildren()[1].toTLA(false);
		  Map<String,String> mp = new HashMap<>();
		  mp.put(var, type);
		  return mp;
	  }
	  
	  // merge all maps
	  return Utils.toArrayList(getChildren())
			  .stream()
			  .reduce(new HashMap<String,String>(),
					  (acc, c) -> {
						  acc.putAll(c.collectTypesFromTypeOK());
						  return acc;
					  },
					  (m1, m2) -> {
						 m1.putAll(m2);
						 return m1;
					  });
  }
  
  @Override
  public void removeMalformedChildren() {
	  // we want to remove at the conjunct/disjunct level ideally
	  if (this.operands != null) {
		  this.operands = Utils.toArrayList(this.operands)
				  .stream()
				  .filter(o -> !o.isMalformed())
				  .toArray(ExprOrOpArgNode[]::new);
	  }
	  if (getChildren() != null) {
		  for (SemanticNode n : getChildren()) {
			  n.removeMalformedChildren();
		  }
	  }
  }
  
  @Override
  public boolean isMalformed() {
	  return !isCorrectlyFormed() ||
			  Utils.toArrayList(getChildren())
				  .stream()
				  .anyMatch(c -> c.isMalformed());
  }
  
  @Override
  public void stateVarVisit(Set<String> vars) {
	  final SymbolNode op = this.getOperator();
	  if (op.getKind() == VariableDeclKind) {
		  //final OpDeclNode varNode = (OpDeclNode) op;
		  final String name = op.getName().toString();
		  vars.add(name);
	  }
	  
	  if (getChildren() != null) {
		  for (SemanticNode n : getChildren()) {
			  n.stateVarVisit(vars);
		  }
	  }
  }
  
  @Override
  public void removeChildrenWithName(final Set<String> toRemove) {
	  // for bounded quants
	  for (ExprNode n : this.ranges) {
		  if (n.containsStateVars(toRemove)) {
			  isSetMalformed = true;
			  return;
		  }
	  }
	  
	  if (getChildren() != null) {
		  final SymbolNode opNode = this.getOperator();
		  final String opKey = opNode.getName().toString();
		  
		  final int origLen = this.operands.length;
		  this.operands = Utils.toArrayList(this.operands)
				  .stream()
				  .filter(d -> {
					  if (d instanceof OpApplNode) {
						  final OpApplNode child = (OpApplNode) d;
						  final String name = child.getOperator().getName().toString();
						  return !toRemove.contains(name);
					  }
					  return true;
				  })
				  .toArray(ExprOrOpArgNode[]::new);
		  
		  // function appl with just 1 arg is a state var..so we need to track that this causes an issue
		  // op calls with with fewer calls will be an error that we can't detect later, so track this too
		  // we can detect other op errors later, afaik
		  if (isFcnApply(opKey) || isOpCall(opKey)) {
			  if (this.operands.length < origLen) {
				  isSetMalformed = true;
			  }
		  }
		  
		  for (SemanticNode n : getChildren()) {
			  n.removeChildrenWithName(toRemove);
		  }
	  }
  }
  
  public void removeConjunctsWithEmptyUnchangedOp() {
	  if (getChildren() != null) {
		  final SymbolNode opNode = this.getOperator();
		  final String opKey = opNode.getName().toString();
		  
		  if (opKey.equals("$ConjList")) {
			  this.operands = Utils.toArrayList(this.operands)
				.stream()
				.filter(c -> {
					if (c instanceof OpApplNode) {
						final OpApplNode cNode = (OpApplNode) c;
						final String cKey = cNode.getOperator().getName().toString();
						if (isUnchangedOp(cKey) && cNode.operands.length == 1) {
							final ExprOrOpArgNode child = cNode.operands[0];
							Utils.assertTrue(child instanceof OpApplNode, "UNCHANGED should be applied to an OpApplNode!");
							final OpApplNode childNode = (OpApplNode) child;
							final String childKey = childNode.getOperator().getName().toString();
							if (childKey.equals("$Tuple")) {
								if (childNode.operands.length == 0) {
									return false;
								}
							}
						}
					}
					return true;
				})
				.toArray(ExprOrOpArgNode[]::new);
		  }
		  
		  // notice we only remove the top level conjuncts, i.e. we don't recurse once we remove
		  else {
			  for (SemanticNode n : getChildren()) {
				  n.removeConjunctsWithEmptyUnchangedOp();
			  }
		  }
	  }
  }
  
  @Override
  public boolean containsStateVars(final Set<String> vars) {
	  final SymbolNode opNode = this.getOperator();
	  final String opKey = opNode.getName().toString();
	  if (getChildren() == null || getChildren().length == 0) {
		  if (vars.contains(opKey)) {
			  return true;
		  }
	  }
	  if (getChildren() == null) {
		  return false;
	  }
	  return Utils.toArrayList(getChildren())
			  .stream()
			  .anyMatch(c -> c.containsStateVars(vars));
  }
  
  @Override
  public boolean containsNodeOrDefWithName(final String name, final List<OpDefNode> moduleNodes) {
	  final SymbolNode opNode = this.getOperator();
	  final String opKey = opNode.getName().toString();
	  if (opKey.equals(name)) {
		  return true;
	  }
	  
	  // if the node is a user defined op then we need to search the def for state vars
	  final List<OpDefNode> opDefinition = moduleNodes
			  .stream()
			  .filter(n -> opKey.equals(n.getName().toString()))
			  .collect(Collectors.toList());
	  Utils.assertTrue(opDefinition.size() <= 1, "Multiple moduleNodes with the same name is not possible!");
	  final boolean isUserDefinedOp = opDefinition.size() > 0;
	  if (isUserDefinedOp) {
		  final OpDefNode defNode = opDefinition.get(0);
		  final boolean defContainsNodeWithName = defNode.containsNodeOrDefWithName(name, moduleNodes);
		  if (defContainsNodeWithName) {
			  return true;
		  }
	  }
	  
	  if (getChildren() == null) {
		  return false;
	  }
	  return Utils.toArrayList(getChildren())
			  .stream()
			  .anyMatch(c -> c.containsNodeOrDefWithName(name, moduleNodes));
  }
  
  @Override
  public boolean containsNodeOrDefWithNames(final Set<String> names, final List<OpDefNode> moduleNodes) {
	  final SymbolNode opNode = this.getOperator();
	  final String opKey = opNode.getName().toString();
	  if (names.contains(opKey)) {
		  return true;
	  }
	  
	  // if the node is a user defined op then we need to search the def for state vars
	  final List<OpDefNode> opDefinition = moduleNodes
			  .stream()
			  .filter(n -> opKey.equals(n.getName().toString()))
			  .collect(Collectors.toList());
	  Utils.assertTrue(opDefinition.size() <= 1, "Multiple moduleNodes with the same name is not possible!");
	  final boolean isUserDefinedOp = opDefinition.size() > 0;
	  if (isUserDefinedOp) {
		  final OpDefNode defNode = opDefinition.get(0);
		  final boolean defContainsNodeWithName = defNode.containsNodeOrDefWithNames(names, moduleNodes);
		  if (defContainsNodeWithName) {
			  return true;
		  }
	  }
	  
	  if (getChildren() == null) {
		  return false;
	  }
	  return Utils.toArrayList(getChildren())
			  .stream()
			  .anyMatch(c -> c.containsNodeOrDefWithNames(names, moduleNodes));
  }
  
  @Override
  public boolean containsNodeWithName(final String name) {
	  final SymbolNode opNode = this.getOperator();
	  final String opKey = opNode.getName().toString();
	  if (opKey.equals(name)) {
		  return true;
	  }
	  if (getChildren() == null) {
		  return false;
	  }
	  return Utils.toArrayList(getChildren())
			  .stream()
			  .anyMatch(c -> c.containsNodeWithName(name));
  }
  
  @Override
  public boolean containsNodeWithAnyName(final Set<String> names) {
	  final SymbolNode opNode = this.getOperator();
	  final String opKey = opNode.getName().toString();
	  if (names.contains(opKey)) {
		  return true;
	  }
	  if (getChildren() == null) {
		  return false;
	  }
	  return Utils.toArrayList(getChildren())
			  .stream()
			  .anyMatch(c -> c.containsNodeWithAnyName(names));
  }
  
  @Override
  public boolean hasUnchangedNode() {
	  final SymbolNode opNode = this.getOperator();
	  final String opKey = opNode.getName().toString();
	  if (isUnchangedOp(opKey)) {
		  return true;
	  }

	  if (getChildren() == null) {
		  return false;
	  }
	  return Utils.toArrayList(getChildren())
			  .stream()
			  .anyMatch(c -> c.hasUnchangedNode());
  }

  @Override
  public boolean hasOnlyUnchangedConjuncts() {
	  final SemanticNode[] children = getChildren();
	  if (children == null) {
		  return false;
	  }
	  
	  final SymbolNode opNode = this.getOperator();
	  final String opKey = opNode.getName().toString();
	  if (opKey.equals("$ConjList")) {
		  return Utils.toArrayList(getChildren())
		  	.stream()
		  	.allMatch(c -> c.hasUnchangedNode());
	  }
	  
	  return children.length > 0 &&
			  Utils.toArrayList(getChildren())
				  .stream()
				  .allMatch(c -> c.hasOnlyUnchangedConjuncts());
  }
  
  @Override
  public boolean varIsUnchanged(final String var) {
	  final SymbolNode opNode = this.getOperator();
	  final String opKey = opNode.getName().toString();
	  if (isUnchangedOp(opKey)) {
		  final boolean varIsUnchanged = Utils.toArrayList(getChildren())
				  .stream()
				  .anyMatch(c -> c.containsNodeWithName(var));
		  if (varIsUnchanged) {
			  return true;
		  }
	  }
	  
	  if (getChildren() == null) {
		  return false;
	  }
	  return Utils.toArrayList(getChildren())
			  .stream()
			  .anyMatch(c -> c.varIsUnchanged(var));
  }
  
  @Override
  public boolean varOccursInGuard(final String var) {
	  if (getChildren() == null) {
		  return false;
	  }

	  final SymbolNode opNode = this.getOperator();
	  final String opKey = opNode.getName().toString();
	  if (opKey.equals("$ConjList")) {
		  // check each conjunct separately. do not consider UNCHANGED conjuncts though.
		  return Utils.toArrayList(getChildren())
				  .stream()
				  .anyMatch(c -> !c.hasUnchangedNode() && c.containsNodeWithName(var) && !c.hasPrimedOp());
	  }
	  else {
		  return Utils.toArrayList(getChildren())
				  .stream()
				  .anyMatch(c -> c.varOccursInGuard(var));
	  }
  }

  @Override
  public boolean hasPrimedOp() {
	  final SymbolNode opNode = this.getOperator();
	  final String opKey = opNode.getName().toString();
	  if (isPrimeOp(opKey)) {
		  return true;
	  }
	  if (getChildren() == null) {
		  return false;
	  }
	  return Utils.toArrayList(getChildren())
			  .stream()
			  .anyMatch(c -> c.hasPrimedOp());
  }
  
  @Override
  public boolean emptyNode() {
	  final SymbolNode opNode = this.getOperator();
	  final String opKey = opNode.getName().toString();
	  //if (isInfixOp(opKey)) {
	  if (opKey.equals("$ConjList")) {
		  if (getChildren() == null) {
			  return true;
		  }
		  return Utils.toArrayList(getChildren())
				  .stream()
				  .allMatch(c -> c.emptyNode());
	  }
	  
	  if (getChildren() == null || getChildren().length == 0) {
		  return false;
	  }
	  return Utils.toArrayList(getChildren())
			  .stream()
			  .allMatch(c -> c.emptyNode());
  }
  
  @Override
  protected Set<String> stateVarsThatOccurInVars(final Set<String> notInVars, final Set<String> vars, final List<OpDefNode> defExpansionNodes, boolean inConjunct) {
	  final SymbolNode opNode = this.getOperator();
	  final String opKey = opNode.getName().toString();
	  final boolean enteredConjunct = inConjunct || opKey.equals("$ConjList");
	  final boolean isLeaf = this.getChildren() == null || this.getChildren().length == 0;
	  if (isExprNode(opKey) || (isBoundedQuant(opKey) && inConjunct) || isLeaf) {
		  /*
		  final Set<String> allStateVars = Utils.union(vars, notInVars);
		  final Set<String> exprVars = this.stateVarsInFormula(allStateVars, defExpansionNodes);
		  if (!Utils.intersection(vars, exprVars).isEmpty() && !Utils.intersection(notInVars, exprVars).isEmpty()) {
			  return Utils.union(vars, Utils.intersection(notInVars, exprVars));
		  }*/
		  //if (this.containsNodeOrDefWithNames(vars,defExpansionNodes)) {
		  
		  if (this.containsStateVars(vars)) {
			  // at least one of the state vars in <vars> occurs in this expr
			  return notInVars
					  .stream()
					  .filter(v -> this.containsNodeOrDefWithName(v,defExpansionNodes))
					  .collect(Collectors.toSet());
		  }
		  else {
			  // no state vars in <vars> occur in this expr
			  return new HashSet<>();
		  }
	  }
	  else {
		  return Utils.toArrayList(getChildren())
				  .stream()
				  .reduce(vars,
						  (acc, n) -> Utils.union(acc, n.stateVarsThatOccurInVars(notInVars,vars,defExpansionNodes,enteredConjunct)),
						  (n, m) -> Utils.union(n, m));
	  }
  }
  
  @Override
  public Set<String> stateVarsOutsideOfUNCHANGED(final Set<String> varNames, final List<OpDefNode> defExpansionNodes) {
	  Set<String> vars = new HashSet<>();
	  
	  final SymbolNode opNode = this.getOperator();
	  final String opKey = opNode.getName().toString();
	  
	  // do not search through UNCHANGED blocks
	  if (isUnchangedOp(opKey)) {
		  return vars;
	  }
	  
	  // add state variables
	  if (varNames.contains(opKey)) {
		  vars.add(opKey);
	  }
	  
	  // if the node is a user defined op then we need to search the def for state vars
	  final List<OpDefNode> opDefinition = defExpansionNodes
			  .stream()
			  .filter(n -> opKey.equals(n.getName().toString()))
			  .collect(Collectors.toList());
	  Utils.assertTrue(opDefinition.size() <= 1, "Multiple moduleNodes with the same name is not possible!");
	  final boolean isUserDefinedOp = opDefinition.size() > 0;
	  if (isUserDefinedOp) {
		  final OpDefNode defNode = opDefinition.get(0);
		  vars.addAll(defNode.stateVarsOutsideOfUNCHANGED(varNames,defExpansionNodes));
	  }
	  
	  if (getChildren() == null) {
		  return vars;
	  }
	  return Utils.toArrayList(getChildren())
			  .stream()
			  .reduce(vars,
					  (acc, n) -> Utils.union(acc, n.stateVarsOutsideOfUNCHANGED(varNames,defExpansionNodes)),
					  (n, m) -> Utils.union(n, m));
  }
  
  @Override
  protected Set<String> primedStateVarsOutsideOfUNCHANGED(final Set<String> varNames, final List<OpDefNode> defExpansionNodes, boolean inPrime) {
	  Set<String> vars = new HashSet<>();
	  
	  final SymbolNode opNode = this.getOperator();
	  final String opKey = opNode.getName().toString();
	  
	  // do not search through UNCHANGED blocks
	  if (isUnchangedOp(opKey)) {
		  return vars;
	  }
	  
	  inPrime = inPrime || isPrimeOp(opKey);
	  
	  // add state variables if it's primed
	  if (inPrime && varNames.contains(opKey)) {
		  vars.add(opKey);
	  }
	  
	  // if the node is a user defined op then we need to search the def for state vars
	  final List<OpDefNode> opDefinition = defExpansionNodes
			  .stream()
			  .filter(n -> opKey.equals(n.getName().toString()))
			  .collect(Collectors.toList());
	  Utils.assertTrue(opDefinition.size() <= 1, "Multiple moduleNodes with the same name is not possible!");
	  final boolean isUserDefinedOp = opDefinition.size() > 0;
	  if (isUserDefinedOp) {
		  final OpDefNode defNode = opDefinition.get(0);
		  vars.addAll(defNode.primedStateVarsOutsideOfUNCHANGED(varNames,defExpansionNodes,inPrime));
	  }
	  
	  if (getChildren() == null) {
		  return vars;
	  }
	  final boolean finalInPrime = inPrime;
	  return Utils.toArrayList(getChildren())
			  .stream()
			  .reduce(vars,
					  (acc, n) -> Utils.union(acc, n.primedStateVarsOutsideOfUNCHANGED(varNames,defExpansionNodes,finalInPrime)),
					  (n, m) -> Utils.union(n, m));
  }
  
  @Override
  public Set<String> unprimedStateVarsOutsideOfUNCHANGED(final Set<String> varNames, final List<OpDefNode> defExpansionNodes) {
	  Set<String> vars = new HashSet<>();
	  
	  final SymbolNode opNode = this.getOperator();
	  final String opKey = opNode.getName().toString();
	  
	  // do not search through UNCHANGED blocks or primed vars
	  if (isUnchangedOp(opKey) || isPrimeOp(opKey)) {
		  return vars;
	  }
	  
	  // add state variables
	  if (varNames.contains(opKey)) {
		  vars.add(opKey);
	  }
	  
	  // if the node is a user defined op then we need to search the def for state vars
	  final List<OpDefNode> opDefinition = defExpansionNodes
			  .stream()
			  .filter(n -> opKey.equals(n.getName().toString()))
			  .collect(Collectors.toList());
	  Utils.assertTrue(opDefinition.size() <= 1, "Multiple moduleNodes with the same name is not possible!");
	  final boolean isUserDefinedOp = opDefinition.size() > 0;
	  if (isUserDefinedOp) {
		  final OpDefNode defNode = opDefinition.get(0);
		  vars.addAll(defNode.unprimedStateVarsOutsideOfUNCHANGED(varNames,defExpansionNodes));
	  }
	  
	  if (getChildren() == null) {
		  return vars;
	  }
	  return Utils.toArrayList(getChildren())
			  .stream()
			  .reduce(vars,
					  (acc, n) -> Utils.union(acc, n.unprimedStateVarsOutsideOfUNCHANGED(varNames,defExpansionNodes)),
					  (n, m) -> Utils.union(n, m));
  }
  
  @Override
  public int numOccurrencesOutsideOfUNCHANGED(final String var) {
	  final SymbolNode opNode = this.getOperator();
	  final String opKey = opNode.getName().toString();
	  
	  // do not search through UNCHANGED blocks
	  if (isUnchangedOp(opKey)) {
		  return 0;
	  }
	  
	  // if we found a match, then there is 1 occurrence in this node
	  if (opKey.equals(var)) {
		  return 1;
	  }
	  
	  if (getChildren() == null) {
		  return 0;
	  }
	  return Utils.toArrayList(getChildren())
			  .stream()
			  .reduce(0,
					  (acc, n) -> acc + n.numOccurrencesOutsideOfUNCHANGED(var),
					  (n, m) -> n + m);
  }
  
  @Override
  public boolean isGuarded() {
	  if (getChildren() == null) {
		  return false;
	  }

	  final SymbolNode opNode = this.getOperator();
	  final String opKey = opNode.getName().toString();
	  if (opKey.equals("$ConjList")) {
		  // check each conjunct separately. do not consider UNCHANGED conjuncts though.
		  return Utils.toArrayList(getChildren())
				  .stream()
				  .anyMatch(c -> !c.hasUnchangedNode() && !c.hasPrimedOp());
	  }
	  else {
		  return Utils.toArrayList(getChildren())
				  .stream()
				  .anyMatch(c -> c.isGuarded());
	  }
  }
  
  /**
   * WARNING: this method is untested.
   */
  @Override
  public Set<String> stateVarsInFormula(final Set<String> varNames, final List<OpDefNode> defExpansionNodes) {
	  Set<String> vars = new HashSet<>();
	  
	  final SymbolNode opNode = this.getOperator();
	  final String opKey = opNode.getName().toString();
	  if (varNames.contains(opKey)) {
		  vars.add(opKey);
	  }
	  
	  // if the node is a user defined op then we need to search the def for state vars
	  final List<OpDefNode> opDefinition = defExpansionNodes
			  .stream()
			  .filter(n -> opKey.equals(n.getName().toString()))
			  .collect(Collectors.toList());
	  Utils.assertTrue(opDefinition.size() <= 1, "Multiple moduleNodes with the same name is not possible!");
	  final boolean isUserDefinedOp = opDefinition.size() > 0;
	  if (isUserDefinedOp) {
		  final OpDefNode defNode = opDefinition.get(0);
		  vars.addAll(defNode.stateVarsInFormula(varNames, defExpansionNodes));
	  }
	  
	  if (getChildren() == null) {
		  return vars;
	  }
	  return Utils.toArrayList(getChildren())
			  .stream()
			  .reduce(vars,
					  (acc, n) -> Utils.union(acc, n.stateVarsInFormula(varNames,defExpansionNodes)),
					  (n, m) -> Utils.union(n, m));
  }
  
  private static boolean isExprNode(final String key) {
	  // TODO there's several missing operators here
	  return key.equals("=")
			  || key.equals("/=")
			  || key.equals("#")
			  || key.equals(">")
			  || key.equals("<")
			  || key.equals(">=")
			  || key.equals("<=")
			  || key.equals("\\leq")
			  || key.equals("\\geq")
			  || key.equals("+")
			  || key.equals("-")
			  || key.equals("*")
			  || key.equals("\\div")
			  || key.equals("=>")
			  || key.equals("\\")
			  || key.equals("\\union")
			  || key.equals("\\intersect")
			  || key.equals("\\in")
			  || key.equals("\\notin")
			  || key.equals("\\lnot")
			  || key.equals("$IfThenElse");
  }
  
  @Override
  protected String toTLA(boolean pretty) {
	  final SymbolNode opNode = this.getOperator();
	  final String opKey = opNode.getName().toString();
	  final String op = keyToOp(opKey);
	  
	  if (getChildren() == null || (getChildren().length == 0 && !op.contains("$"))) {
		  return op;
	  }
	  else {
		  // infix ops
		  if (isInfixOp(opKey)) {
			  final boolean usePretty = pretty && (op.equals("/\\") || op.equals("\\/"));
			  final String prefix = usePretty ? op + " " : "";
			  final String paddedOp = usePretty ? "\n" + op + " " : " " + op + " ";
			  final String childrenToTLA = Utils.toArrayList(getChildren())
			  	.stream()
			  	.map(c -> c.toTLA(false))
			  	.collect(Collectors.joining(paddedOp));
			  if (!usePretty && getChildren().length > 1 && !dontUseParens(op)) {
				  return "(" + prefix + childrenToTLA + ")";
			  }
			  else {
				  return prefix + childrenToTLA;
			  }
		  }
		  
		  // bounded quants + CHOOSE
		  else if (isBoundedQuant(opKey) || isBoundedChoose(opKey)) {
			  final FormalParamNode[][] paramsPerDomain = getBdedQuantSymbolLists();
			  final ExprNode[] domainNodes = this.ranges;
			  ArrayList<String> declList = new ArrayList<>();
			  Utils.assertTrue(paramsPerDomain.length == domainNodes.length, "Length mismatch in bounded quant/choose between domains and params!");
			  
			  for (int i = 0; i < domainNodes.length; ++i) {
				  final String domain = domainNodes[i].toTLA(false);
				  final String qvars = Utils.toArrayList(paramsPerDomain[i])
						  .stream()
						  .map(p -> p.getName().toString())
						  .collect(Collectors.joining(","));
				  final String decl = qvars + " \\in " + domain;
				  declList.add(decl);
			  }

			  Utils.assertTrue(operands.length > 0, "Bounded quant/choose should have at least one operand for the body!");
			  final String body = operands[0].toTLA(pretty);
			  final String quantMatrixSep = pretty ? " :\n" : " : ";
			  final String decls = String.join(", ", declList);
			  
			  if (pretty) {
				  return op + " " + decls + quantMatrixSep + body;
			  }
			  else {
				  return "(" + op + " " + decls + quantMatrixSep + body + ")";
			  }
		  }
		  
		  // prime op
		  else if (isPrimeOp(opKey)) {
			  Utils.assertTrue(getChildren().length == 1, "Prime op should only be applied to a single arg!");
			  return getChildren()[0].toTLA(false) + opKey;
		  }

		  // UNCHANGED op
		  else if (isUnchangedOp(opKey)) {
			  Utils.assertTrue(getChildren().length == 1, "UNCHANGED op should only be applied to a single arg!");
			  return opKey + " " + getChildren()[0].toTLA(false);
		  }

		  // logical NOT op
		  else if (isNotOp(opKey)) {
			  Utils.assertTrue(getChildren().length == 1, "~ op should only be applied to a single arg!");
			  return op + "(" + getChildren()[0].toTLA(false) + ")";
		  }
		  
		  // tuples
		  else if (isTupleOp(opKey)) {
			  final String childrenToTLA = Utils.toArrayList(getChildren())
			  	.stream()
			  	.map(c -> c.toTLA(false))
			  	.collect(Collectors.joining(","));
			  return "<<" + childrenToTLA + ">>";
		  }
		  
		  // set enumeration op
		  else if (isSetEnumerateOp(opKey)) {
			  final String childrenToTLA = Utils.toArrayList(getChildren())
			  	.stream()
			  	.map(c -> c.toTLA(false))
			  	.collect(Collectors.joining(","));
			  return "{" + childrenToTLA + "}";
		  }
		  
		  // indexing into functions and records
		  else if (isFunctionOrRecordIndex(opKey)) {
			  // whether or not we use [] (for functions) or . (for records) depends on whether
			  // an entry has quotes. this is pretty crazy, but see OpDefNode.java:121 for an explanation
			  // (this only occurs within an EXCEPT).
			  final String childrenToTLA = Utils.toArrayList(getChildren())
					  	.stream()
					  	.map(c -> c.toTLA(false))
					  	.map(c -> {
					  		// if <c> contains a quote, then it should be treated like a record
					  		if (c.contains("\"")) {
					  			return "." + c;
					  		}
					  		// otherwise, if <c> doesn't have a quote, it should be treated like a function
					  		return "[" + c + "]";
					  	})
					  	.collect(Collectors.joining(""));
			  return childrenToTLA;
		  }
		  
		  // record constructor
		  else if (isRcdConstructor(opKey)) {
			  final String childrenToTLA = Utils.toArrayList(getChildren())
					  	.stream()
					  	.map(r -> r.toTLA(false))
					  	.collect(Collectors.joining(","));
			  return "[" + childrenToTLA + "]";
		  }
		  
		  // function application op
		  else if (isFcnApply(opKey)) {
			  switch (getChildren().length) {
			  case 1:
				  // state variable
				  return getChildren()[0].toTLA(false);
			  case 2:
				  // function application
				  final String func = getChildren()[0].toTLA(false);
				  final String args = getChildren()[1].toTLA(false);
				  return func + "[" + args + "]";
			  default:
				  Utils.assertTrue(false, "Function applications must have 1 or 2 args!");
				  return null;
			  }
		  }
		  
		  // EXCEPT op
		  else if (isExcept(opKey)) {
			  Utils.assertTrue(getChildren().length == 2, "EXCEPT op must have exactly 2 args!");
			  final String func = getChildren()[0].toTLA(false);
			  final String exception = getChildren()[1].toTLA(false);
			  return "[" + func + " EXCEPT!" + exception + "]";
		  }
		  
		  // pair, I guess an equality?
		  else if (isPair(opKey)) {
			  Utils.assertTrue(getChildren().length == 2, "Pair op must have exactly 2 args!");
			  final boolean isRecord = getChildren()[0].toTLA(false).matches("^\".*\"$"); // hacky way of detecting records
			  final String assignmentOperator = isRecord ? " |-> " : " = ";
			  final String lhs = getChildren()[0].toTLA(false).replace("\"", ""); // remove quotes for record keys
			  final String rhs = getChildren()[1].toTLA(false);
			  return lhs + assignmentOperator + rhs;
		  }
		  
		  // function constructor, I'll assume a constant value for now
		  else if (isFcnConstructor(opKey)) {
			  Utils.assertTrue(getChildren().length == 2, "We assume function constructors have exactly 2 args!");
			  final FormalParamNode[][] paramsPerDomain = getBdedQuantSymbolLists();
			  Utils.assertTrue(paramsPerDomain.length == 1, "We currently only support quantification over a single domain at a time.");
			  final FormalParamNode[] params = paramsPerDomain[0];
			  
			  final String domain = getChildren()[0].toTLA(false);
			  final String qvars = Utils.toArrayList(params)
					  .stream()
					  .map(p -> p.getName().toString())
					  .collect(Collectors.joining(","));
			  final String val = getChildren()[1].toTLA(false);
			  return "[" + qvars + " \\in " + domain + " |-> " + val + "]";
		  }
		  
		  // set of functions
		  else if (isSetOfFcns(opKey)) {
			  Utils.assertTrue(getChildren().length == 2, "We assume that function sets have exactly 2 args!");
			  final String domain = getChildren()[0].toTLA(false);
			  final String range = getChildren()[1].toTLA(false);
			  return "[" + domain + " -> " + range + "]";
		  }
		  
		  // set of records
		  else if (isSetOfRcds(opKey)) {
			  final String body = Utils.toArrayList(this.operands)
					  .stream()
					  .map(r -> r.toTLA(false))
					  .map(r -> r.replace("=", ":"))
					  .collect(Collectors.joining(","));
			  return "[" + body + "]";
		  }
		  
		  // set comprehension (with domain first, i.e. {x \in D | C(x)})
		  else if (isSubsetOf(opKey)) {
			  Utils.assertTrue(getChildren().length == 2, "SubsetOf (set comprehension) must have exactly 2 args!");
			  final FormalParamNode[][] paramsPerDomain = getBdedQuantSymbolLists();
			  Utils.assertTrue(paramsPerDomain.length == 1, "We currently only support quantification over a single domain at a time.");
			  final FormalParamNode[] params = paramsPerDomain[0];
			  
			  final boolean qvarsAreInATuple = tupleOrs.length > 0 && tupleOrs[0];
			  final String rawQvars = Utils.toArrayList(params)
					  .stream()
					  .map(p -> p.getName().toString())
					  .collect(Collectors.joining(","));
			  final String qvars = qvarsAreInATuple ? "<<" + rawQvars + ">>" : rawQvars;
			  final String domain = getChildren()[0].toTLA(false);
			  final String body = getChildren()[1].toTLA(false);
			  return "{ " + qvars + " \\in " + domain + " : " + body + " }";
		  }
		  
		  // set comprehension (with domain second, i.e. {E(x) | x \in D})
		  else if (isSetOfAll(opKey)) {
			  Utils.assertTrue(getChildren().length == 2, "SetOfAll (set comprehension) must have exactly 2 args!");
			  final FormalParamNode[][] paramsPerDomain = getBdedQuantSymbolLists();
			  Utils.assertTrue(paramsPerDomain.length == 1, "We currently only support quantification over a single domain at a time.");
			  final FormalParamNode[] params = paramsPerDomain[0];
			  
			  final String domain = getChildren()[0].toTLA(false);
			  final String qvars = Utils.toArrayList(params)
					  .stream()
					  .map(p -> p.getName().toString())
					  .collect(Collectors.joining(","));
			  final String expr = getChildren()[1].toTLA(false);
			  return "{ " + expr + " : " + qvars + " \\in " + domain + " }";
		  }
		  
		  // . operator for records
		  else if (isRcdSelect(opKey)) {
			  Utils.assertTrue(getChildren().length == 2, "RcdSelect (.) must have exactly 2 args!");
			  final String lhs = getChildren()[0].toTLA(false);
			  final String rhs = getChildren()[1].toTLA(false).replace("\"", ""); // remove quotes from the field
			  return lhs + "." + rhs;
		  }
		  
		  // IF-THEN-ELSE
		  else if (isITE(opKey)) {
			  Utils.assertTrue(getChildren().length == 3, "IF-THEN-ELSE must have exactly 3 args!");
			  final String cond = getChildren()[0].toTLA(false);
			  final String tCond = getChildren()[1].toTLA(false);
			  final String fCond = getChildren()[2].toTLA(false);
			  return "IF " + cond + " THEN " + tCond + " ELSE " + fCond;
		  }
		  
		  // inside of the [] temporal op
		  else if (isSquareAct(opKey)) {
			  Utils.assertTrue(getChildren().length == 2, "SquareAct op should have exactly 2 args!");
			  final String body = getChildren()[0].toTLA(false);
			  final String stutVars = getChildren()[1].toTLA(false);
			  return "[" + body + "]_" + stutVars;
		  }
		  
		  // [] temporal op
		  else if (isAlwaysTemporalOp(opKey)) {
			  Utils.assertTrue(getChildren().length == 1, "[] op should have exactly 1 arg!");
			  final String body = getChildren()[0].toTLA(false);
			  return op + body;
		  }
		  
		  // either:
		  // 1) this is an operator call or
		  // 2) this is something unexpected, and we print it like an operator call
		  else {
			  final String childrenToTLA = Utils.toArrayList(getChildren())
					  	.stream()
					  	.map(c -> c.toTLA(false))
					  	.collect(Collectors.joining(","));
			  return opKey + "(" + childrenToTLA + ")";
		  }
	  }
  }
  
  private static boolean isPrimeOp(final String key) {
	  return key.equals("'");
  }
  
  private static boolean isUnchangedOp(final String key) {
	  return key.equals("UNCHANGED");
  }
  
  private static boolean isNotOp(final String key) {
	  return key.equals("\\lnot");
  }
  
  private static boolean isTupleOp(final String key) {
	  return key.equals("$Tuple");
  }
  
  private static boolean isSetEnumerateOp(final String key) {
	  return key.equals("$SetEnumerate");
  }
  
  private static boolean isFunctionOrRecordIndex(final String key) {
	  return key.equals("$Seq");
  }
  
  private static boolean isRcdConstructor(final String key) {
	  return key.equals("$RcdConstructor");
  }
  
  private static boolean isFcnApply(final String key) {
	  return key.equals("$FcnApply");
  }
  
  private static boolean isExcept(final String key) {
	  return key.equals("$Except");
  }
  
  private static boolean isPair(final String key) {
	  return key.equals("$Pair");
  }
  
  private static boolean isFcnConstructor(final String key) {
	  return key.equals("$FcnConstructor");
  }
  
  private static boolean isSetOfFcns(final String key) {
	  return key.equals("$SetOfFcns");
  }
  
  private static boolean isSetOfRcds(final String key) {
	  return key.equals("$SetOfRcds");
  }
  
  private static boolean isSubsetOf(final String key) {
	  return key.equals("$SubsetOf");
  }
  
  private static boolean isSetOfAll(final String key) {
	  return key.equals("$SetOfAll");
  }
  
  private static boolean isRcdSelect(final String key) {
	  return key.equals("$RcdSelect");
  }
  
  private static boolean isITE(final String key) {
	  return key.equals("$IfThenElse");
  }
  
  private static boolean isSquareAct(final String key) {
	  return key.equals("$SquareAct");
  }
  
  private static boolean isAlwaysTemporalOp(final String key) {
	  return key.equals("[]");
  }
  
  private static boolean isBoundedChoose(final String key) {
	  return key.equals("$BoundedChoose");
  }
  
  private static boolean isBoundedQuant(final String key) {
	  return key.equals("$BoundedExists")
			  || key.equals("$BoundedForall");
  }
  
  private static boolean dontUseParens(final String key) {
	  return key.equals("=")
			  || key.equals("/=")
			  || key.equals("#")
			  || key.equals(">")
			  || key.equals("<")
			  || key.equals(">=")
			  || key.equals("<=")
			  || key.equals("\\n");
  }
  
  private static boolean isInfixOp(final String key) {
	  return key.equals("=")
			  || key.equals("/=")
			  || key.equals("#")
			  || key.equals(">")
			  || key.equals("<")
			  || key.equals(">=")
			  || key.equals("<=")
			  || key.equals("\\leq")
			  || key.equals("\\geq")
			  || key.equals("+")
			  || key.equals("-")
			  || key.equals("*")
			  || key.equals("\\div")
			  || key.equals("=>")
			  || key.equals("$ConjList")
			  || key.equals("$DisjList")
			  || key.equals("$CartesianProd")
			  || key.equals("\\")
			  || key.equals("\\union")
			  || key.equals("\\intersect")
			  || key.equals("\\in")
			  || key.equals("\\notin")
			  || key.equals("\\land")
			  || key.equals("\\lor");
  }
  
  private static String keyToOp(final String key) {
	  switch (key) {
	  case "$ConjList":
		  return "/\\";
	  case "$DisjList":
		  return "\\/";
	  case "$CartesianProd":
		  return "\\X";
	  case "$BoundedExists":
		  return "\\E";
	  case "$BoundedForall":
		  return "\\A";
	  case "$BoundedChoose":
		  return "CHOOSE";
	  case "\\union":
		  return "\\cup";
	  case "\\intersect":
		  return "\\cap";
	  case "\\land":
		  return "/\\";
	  case "\\lor":
		  return "\\/";
	  case "\\lnot":
		  return "~";
	  case "\\leq":
		  return "<=";
	  case "\\geq":
		  return ">=";
	  default:
		  return key;
	  }
  }
  
  private boolean isCorrectlyFormed() {
	  final SymbolNode opNode = this.getOperator();
	  final String opKey = opNode.getName().toString();
	  
	  if (isSetMalformed) {
		  return false;
	  }
  
	  // infix ops
	  if (isInfixOp(opKey)) {
		  if (opKey.equals("$ConjList") || opKey.equals("$DisjList")) {
			  return getChildren().length >= 1;
		  }
		  return getChildren().length >= 2;
	  }
	  
	  // bounded quants + CHOOSE
	  else if (isBoundedQuant(opKey) || isBoundedChoose(opKey)) {
		  final FormalParamNode[][] paramsPerDomain = getBdedQuantSymbolLists();
		  final ExprNode[] domainNodes = this.ranges;
		  return paramsPerDomain.length == domainNodes.length && operands.length > 0;
	  }
	  
	  // prime op
	  else if (isPrimeOp(opKey)) {
		  return getChildren().length == 1;
	  }

	  // UNCHANGED op
	  else if (isUnchangedOp(opKey)) {
		  return getChildren().length == 1;
	  }

	  // logical NOT op
	  else if (isNotOp(opKey)) {
		  return getChildren().length == 1;
	  }
	  
	  // tuples
	  else if (isTupleOp(opKey)) {
		  return true;
	  }
	  
	  // set enumeration op
	  else if (isSetEnumerateOp(opKey)) {
		  return true;
	  }
	  
	  // function index
	  else if (isFunctionOrRecordIndex(opKey)) {
		  return true;
	  }
	  
	  // record constructor
	  else if (isRcdConstructor(opKey)) {
		  return true;
	  }
	  
	  // function application op
	  else if (isFcnApply(opKey)) {
		  final int numChildren = getChildren().length;
		  return numChildren == 1 || numChildren == 2;
	  }
	  
	  // EXCEPT op
	  else if (isExcept(opKey)) {
		  return getChildren().length == 2;
	  }
	  
	  // pair, I guess an equality?
	  else if (isPair(opKey)) {
		  return getChildren().length == 2;
	  }
	  
	  // function constructor, I'll assume a constant value for now
	  else if (isFcnConstructor(opKey)) {
		  final FormalParamNode[][] paramsPerDomain = getBdedQuantSymbolLists();
		  return getChildren().length == 2 && paramsPerDomain.length == 1;
	  }
	  
	  // set of functions
	  else if (isSetOfFcns(opKey)) {
		  return getChildren().length == 2;
	  }
	  
	  // set of records
	  else if (isSetOfRcds(opKey)) {
		  return true;
	  }
	  
	  // set comprehension (with domain first, i.e. {x \in D | C(x)})
	  else if (isSubsetOf(opKey)) {
		  final FormalParamNode[][] paramsPerDomain = getBdedQuantSymbolLists();
		  return getChildren().length == 2 && paramsPerDomain.length == 1;
	  }
	  
	  // set comprehension (with domain second, i.e. {E(x) | x \in D})
	  else if (isSetOfAll(opKey)) {
		  final FormalParamNode[][] paramsPerDomain = getBdedQuantSymbolLists();
		  return getChildren().length == 2 && paramsPerDomain.length == 1;
	  }
	  
	  // . operator for records
	  else if (isRcdSelect(opKey)) {
		  return getChildren().length == 2;
	  }
	  
	  // IF-THEN-ELSE
	  else if (isITE(opKey)) {
		  return getChildren().length == 3;
	  }
	  
	  // inside of the [] temporal op
	  else if (isSquareAct(opKey)) {
		  return getChildren().length == 2;
	  }
	  
	  // [] temporal op
	  else if (isAlwaysTemporalOp(opKey)) {
		  return getChildren().length == 1;
	  }
	  
	  // either:
	  // 1) this is an operator call or
	  // 2) this is something unexpected, and we print it like an operator call
	  else {
		  return true;
	  }
  }
  
  private static boolean isOpCall(final String opKey) {
	  return !(isInfixOp(opKey)
			  || isBoundedQuant(opKey)
			  || isBoundedChoose(opKey)
			  || isPrimeOp(opKey)
			  || isUnchangedOp(opKey)
			  || isNotOp(opKey)
			  || isTupleOp(opKey)
			  || isSetEnumerateOp(opKey)
			  || isFunctionOrRecordIndex(opKey)
			  || isRcdConstructor(opKey)
			  || isFcnApply(opKey)
			  || isExcept(opKey)
			  || isPair(opKey)
			  || isFcnConstructor(opKey)
			  || isSetOfFcns(opKey)
			  || isSetOfRcds(opKey)
			  || isSubsetOf(opKey)
			  || isSetOfAll(opKey)
			  || isRcdSelect(opKey)
			  || isITE(opKey)
			  || isSquareAct(opKey)
			  || isAlwaysTemporalOp(opKey));
  }

  /**
   *  Returns the node identifying the operator of the operator
   *  application.  For example, for the expression A \cup B, this
   *  points to the OpDefOrDeclNode for \cup.
   */
  public final SymbolNode getOperator() { return this.operator; }

  /**
   * Changes the operator field of this OpApplNode; used only to
   * change nonrecursive function definition operator to recursive
   * when occurrence of operator being defined is encountered on the
   * RHS of the def.
   */
  /*************************************************************************
  * Called only by Function.recursionCheck() in semantic/Generator.java.   *
  *************************************************************************/
  final void resetOperator( UniqueString us ) {
    this.operator = Context.getGlobalContext().getSymbol(us);
  }

  /**
   * Sets the unBoundedBound symbols vector for THIS OpApplNode to null,
   * once it is discoved that a function def is in fact nonrecursive.
   */
  final void makeNonRecursive() { this.unboundedBoundSymbols = null; }

  /**
   * Returns the array of arguments (including operator arguments, but
   * not bound symbols or bounding sets) in the expression.  For
   * example, for the OpApplNode representing the expression
   *
   *    \E x \in S : P
   *
   * it returns a one-element array whose single element is a ref to
   * the ExprNode representing the expression P. The setArgs method
   * sets the value.
   */
  public final ExprOrOpArgNode[] getArgs() { return this.operands; }

  /**
   * Sets the operands array that is returned by getArgs()
   */
  public final void setArgs(ExprOrOpArgNode[] args) { this.operands = args; }

	public final boolean argsContainOpArgNodes() {
		for (ExprOrOpArgNode o : operands) {
			if (o instanceof OpArgNode) {
				return true;
			}
		}
		return false;
	}
  
  /*************************************************************************
  * Despite what you might gather from its 79 character name, this does    *
  * not return the number of bounded bound symbols.  It returns a weird    *
  * count of symbols in which "\A x, y, z \in ..." has 3 symbols but       *
  * "\A <<x, y, z>> \in ..." has only 1.                                   *
  *************************************************************************/
  final int getNumberOfBoundedBoundSymbols() {
    if (this.boundedBoundSymbols == null) return 0;

    int num = 0;
    for (int i = 0; i < this.boundedBoundSymbols.length; i++) {
      if (this.tupleOrs[i]) {
        num++;
      }
      else {
        num += this.boundedBoundSymbols[i].length;
      }
    }
    return num;
  }

  /**
   * These methods identify the OpApplNode's unbounded quantifier
   * symbols. For example, the x, y, and z in
   *
   *     \E x, y, z : P    or   \E <<x, y, z>> : P
   *
   * The method getUnbdedQuantSymbols() returns an array of refs to
   * the FormalParamNodes for x, y, z; and isUnbdedQuantATuple() indicates
   * whether or not there is a << >> around them.
   */
  /*************************************************************************
  * Warning: This seems to return null if there are no unbounded           *
  * quantifier symbols.                                                    *
  *************************************************************************/
  public final FormalParamNode[] getUnbdedQuantSymbols() {
    return this.unboundedBoundSymbols;
  }

  /**
   * For the OpApplNode representing
   *
   *    \E u \in V,  x, y \in S,  <<z, w>> \in R  :  P
   *
   *  - getBdedQuantSymbolLists returns the array of arrays of nodes
   *       [ [u], [x, y], [z, w] ]
   *
   *  - isBdedQuantATuple() returns the array of booleans
   *       [ false, false, true ]
   *
   *  - getBdedQuantBounds() returns the array of nodes
   *       [ V, S, R ]
   */
  public final FormalParamNode[][] getBdedQuantSymbolLists() {
    return boundedBoundSymbols;
  }

  /**
   * @return Union of getBdedQuantSymbolLists (flattened) and getUnbdedQuantSymbols.
   */
  public final List<FormalParamNode> getQuantSymbolLists() {
	  final List<FormalParamNode> l = new ArrayList<>();
		final FormalParamNode[] unbdedQuantSymbols = getUnbdedQuantSymbols();
		if (unbdedQuantSymbols != null) {
			for (final FormalParamNode s : unbdedQuantSymbols) {
				l.add(s);
			}
		}
		final FormalParamNode[][] bdedQuantSymbolLists = getBdedQuantSymbolLists();
		if (bdedQuantSymbolLists != null) {
			for (final FormalParamNode[] outer : bdedQuantSymbolLists) {
				for (final FormalParamNode inner : outer) {
					l.add(inner);
				}
			}
		}
	  return l;
  }

  /**
   * See documentation for getUnbdedQuantSymbols and getBdedQuantSymbolLists()
   */
  public final boolean[] isBdedQuantATuple() { return this.tupleOrs; }

  /**
   * See documentation for getUnbdedQuantSymbols and getBdedQuantSymbolLists()
   */

  /*************************************************************************
  * Eliminated by LL on 3 Aug 2007.  See comments for eliminated isATuple  *
  * field.                                                                 *
  *************************************************************************/
//  public final boolean isUnbdedQuantATuple() { return this.isATuple; }

  /**
   * Returns array of the bound expressions for quantified variables that
   * are bounded in this operator application.
   */
  public final ExprNode[] getBdedQuantBounds() { return this.ranges; }

  private final ExprOrOpArgNode getArg(SymbolNode param) {
    /***********************************************************************
    * If param is a formal parameter of this node's operator, then return  *
    * the operand being substituted for that parameter, else return null.  *
    ***********************************************************************/
    AnyDefNode opDef = (AnyDefNode)this.operator;
    FormalParamNode[] formals = opDef.getParams();
    for (int i = 0; i < this.operands.length; i++) {
      if (formals[i] == param) {
        return this.operands[i];
      }
    }
    return null;
  }

  /* Level Checking */
// These nodes are now part of all LevelNode subclasses.
//  private boolean levelCorrect;
//  private int level;
//  private HashSet levelParams;
//  private SetOfLevelConstraints levelConstraints;
//  private SetOfArgLevelConstraints argLevelConstraints;
//  private HashSet argLevelParams;


/***************************************************************************
* The following was used for debugging.  It might be useful again, so I'm  *
* keeping it here in as a comment.                                         *
***************************************************************************/
// public static void PrintDebugNode(String str) {
//    System.out.print(str + " ");
//    if (debugNode == null) {
//       System.out.println("null node");
//     }
//    else{
//       int savedlevel = debugNode.levelChecked;
//       debugNode.levelChecked = 1;
//       if (debugNode.getAllParams()==null) {
//          System.out.println("allParams null");
//          }
//       else {
//          System.out.println(HashSetToString(debugNode.getAllParams()));
//          };
//    if (debugNode.getAllParams() != debugParams) {
//       System.out.print("allParams changed, old value: ");
//       if (debugParams == null) {
//         System.out.println("null");
//         }
//       else {
//         System.out.println(HashSetToString(debugParams));
//        };
//       debugParams = debugNode.getAllParams();
//        };
//    debugNode.levelChecked = savedlevel;
//    }
// }

  @Override
  public final boolean levelCheck(int itr) {
    if (this.levelChecked >= itr) return this.levelCorrect;
    this.levelChecked = itr ;


    /***********************************************************************
    * Level check all operands[i] and ranges[i]                            *
    ***********************************************************************/
    this.levelCorrect = true;
    for (int i = 0; i < this.operands.length; i++) {
      if (this.operands[i] != null &&
        /*******************************************************************
        * Below, this.operands[i] is dereferenced without first checking   *
        * it for null, so I presume it can't be null.                      *
        *******************************************************************/
          !this.operands[i].levelCheck(itr)) {
        this.levelCorrect = false;
      }
    }
    for (int i = 0; i < this.ranges.length; i++) {
      if (this.ranges[i] != null &&
        /*******************************************************************
        * It appears that this.ranges[i] is never null, because there are  *
        * several places below where this.ranges[i] is dereferenced        *
        * without first checking if it's null.                             *
        *******************************************************************/
          !this.ranges[i].levelCheck(itr)) {

        this.levelCorrect = false;
      }
    }

    // On 24 Oct 2012, LL Changed OpDefNode -> AnyDefNode so this
    // handles ThmnOrAssumpDefNodes as well as OpDefNodes.  See the
    // comments in AnyDefNode.java for an explanation.
    if (this.operator instanceof AnyDefNode) {
      // Application of a builtin or user defined operator
      // Level correctness conditions
      /*********************************************************************
      * Because of the change of bound identifiers from OpDeclNodes to     *
      * FormalParamNodes, the following changes had to be made to the      *
      * level information.                                                 *
      *                                                                    *
      *  - Remove the bound identifier nodes from this.levelParams.        *
      *    In theory, we should set this.level to the maximum of its       *
      *    currently computed value and boundSymbolLevel if such a node    *
      *    is found in this.levelParams.  However, this isn't necessary    *
      *    because boundSymbolLevel > ConstantLevel only for the           *
      *    operators \AA and \EE, which always produce a node of           *
      *    TemporalLevel.                                                  *
      *                                                                    *
      *  - Remove the elements of this.levelConstraints corresponding      *
      *    to the bound identifier nodes.  One should check that the       *
      *    constraint for a bound identifier node does not require its     *
      *    level to be less than boundSymbolLevel, but that's impossible   *
      *    because there are no operators that constrain an argument to    *
      *    have level less than VariableLevel                              *
      *                                                                    *
      *  - Remove from this.argLevelParams all elements alp such that      *
      *    alp.param is a bounded identifier node.  For any such alp,      *
      *    we should also add to this.argLevelConstraints an element       *
      *    alc with alc.param = alp.op, alc.position = alp.i, and value    *
      *    boundSymbolLevel.  However, it's not clear that there's any     *
      *    point to this because an ArgLevelConstraint with a level <=     *
      *    VariableLevel seems to have no practical effect.                *
      *********************************************************************/
      AnyDefNode opDef = (AnyDefNode)this.operator;
      boolean opDefLevelCheck = opDef.levelCheck(itr) ;
        /*******************************************************************
        * Need to call levelCheck before obtaining its level params.       *
        *******************************************************************/
      for (int i = 0; i < this.operands.length; i++) {
        ExprOrOpArgNode opd = this.operands[i];
          /*****************************************************************
          * Note: levelCheck already called on opd.                        *
          *****************************************************************/
        if (opd != null) {
          if (opd.getLevel() > opDef.getMaxLevel(i)) {
            if (opDefLevelCheck && opd.levelCheck(itr)) {
              errors.addError(
                 this.stn.getLocation(),
                 "Level error in applying operator " + opDef.getName() +
                    ":\nThe level of argument " + (i+1) + " exceeds the" +
                    " maximum level allowed by the operator.");
            }
            this.levelCorrect = false;
          }
          // LL changed OpDefNode -> AnyDefNode in the following.
          // See comments in AnyDefNode.java.  (It is only in the
          // most bizarre cases that opd.getOp() would be a
          // ThmOrAssumpDefNode.
          if (opd instanceof OpArgNode &&
              ((OpArgNode)opd).getOp() instanceof AnyDefNode) {
            AnyDefNode opdDef = (AnyDefNode)((OpArgNode)opd).getOp();
            @SuppressWarnings("unused")  // See below comment block
            boolean opdDefLevelCheck = opdDef.levelCheck(itr) ;
              /*************************************************************
              * Need to call opdDef.levelCheck before using its level      *
              * parameters.                                                *
              *************************************************************/
            int alen = opdDef.getArity();
            for (int j = 0; j < alen; j++) {
              if (opdDef.getMaxLevel(j) < opDef.getMinMaxLevel(i, j)) {
                if (opDefLevelCheck && opd.levelCheck(itr)) {
                  errors.addError(this.stn.getLocation(),
                                  "Level error in applying operator "
                                        + opDef.getName() + ":\n" +
                                  "The permitted level of argument "
                                   + (j+1) + " of the operator argument " +
                                  (i+1) + " \nmust be at least " +
                                  opDef.getMinMaxLevel(i, j) + ".");
                }
                this.levelCorrect = false;
              }
            }
            for (int j = 0; j < this.operands.length; j++) {
              for (int k = 0; k < alen; k++) {
                if (opDef.getOpLevelCond(i, j, k) &&
                    this.operands[j].getLevel() > opdDef.getMaxLevel(k)) {
                  if (opd.levelCheck(itr) &&
                      this.operands[j].levelCheck(itr)) {
                    errors.addError(
                       this.stn.getLocation(),
                       "Level error in applying operator " + opDef.getName() +
                         ":\nThe level of argument " + (j+1) + " exceeds the" +
                         " maximum level allowed by the operator.");
                  }
                  this.levelCorrect = false;
                }
              } // for k
            } // for j
          } // if (opd instanceof OpArgNode && ...)
        } // (opd != null)
      } // for i

      for (int i = 0; i < this.ranges.length; i++) {
        ExprNode range = this.ranges[i];
        if (range != null) {
          boolean rangeLevelCheck = range.levelCheck(itr) ;
          if (range.getLevel() > ActionLevel) {
            if (rangeLevelCheck) {
              errors.addError(
                this.stn.getLocation(),
                "Level error in applying operator " + opDef.getName() +
                  ":\nThe level of the range for the bounded variable " +
                  boundedBoundSymbols[i][0] + " \nexceeds the maximum " +
                  "level allowed by the operator.");
            }
            this.levelCorrect = false;
          }
        }
      } // for i

      // Calculate level information
      this.level = opDef.getLevel();
      for (int i = 0; i < this.operands.length; i++) {
        if (this.operands[i] != null &&
            opDef.getWeight(i) == 1) {
          this.level = Math.max(this.level, this.operands[i].getLevel());
        }
      }
      for (int i = 0; i < this.ranges.length; i++) {
        this.level = Math.max(this.level, this.ranges[i].getLevel());
      }

      /*********************************************************************
      * Compute this.levelParams, this.allParams, and                      *
      * this.nonLeibnizParams                                              *
      *********************************************************************/
      this.levelParams.addAll(opDef.getLevelParams());
      this.allParams.addAll(opDef.getAllParams());
      this.nonLeibnizParams.addAll(opDef.getNonLeibnizParams());
      int ar = opDef.getArity() ;
      for (int i = 0; i < this.operands.length; i++) {
        if (this.operands[i] != null &&
            opDef.getWeight(i) == 1) {
          this.levelParams.addAll(this.operands[i].getLevelParams());
        } ;
        if (this.operands[i] != null) {
          /*****************************************************************
          * I'm copying this test from the one for levelParams.  I expect  *
          * it's there in case a null operand was created by an error.     *
          *****************************************************************/
          this.allParams.addAll(this.operands[i].getAllParams());
          this.nonLeibnizParams.addAll(this.operands[i].getNonLeibnizParams());
         };
        int ii = i ;
        if (ar == -1) {ii = 0;} ;
        if (! opDef.getIsLeibnizArg()[ii]) {
          this.nonLeibnizParams.addAll(this.operands[i].getAllParams());
         }
      }
      for (int i = 0; i < this.ranges.length; i++) {
        this.levelParams.addAll(this.ranges[i].getLevelParams());
        this.allParams.addAll(this.ranges[i].getAllParams());
        this.nonLeibnizParams.addAll(this.ranges[i].getNonLeibnizParams());
      }

      /*********************************************************************
      * Set allBoundSymbols to a hashset containing all the                *
      * FormalParamNodes of the bound symbols.                             *
      *********************************************************************/
      HashSet<FormalParamNode> allBoundSymbols = new HashSet<>() ;
      if (this.unboundedBoundSymbols != null) {
        for (int i = 0 ; i < this.unboundedBoundSymbols.length; i++){
          allBoundSymbols.add(this.unboundedBoundSymbols[i]);
         }
       } ;
      if (this.boundedBoundSymbols != null) {
        for (int i = 0 ; i < this.boundedBoundSymbols.length; i++){
          if (this.boundedBoundSymbols[i] != null) {
            for (int j = 0 ; j < this.boundedBoundSymbols[i].length; j++){
              allBoundSymbols.add(this.boundedBoundSymbols[i][j]);
             }
           }
         }
       } ;

      /*********************************************************************
      * Remove bound identifiers from levelParams, allParams, and          *
      * nonLeibnizParams.                                                  *
      *********************************************************************/
      Iterator<FormalParamNode> absIter = allBoundSymbols.iterator() ;
      while (absIter.hasNext()) {
    	  	FormalParamNode nextBoundSymbol = absIter.next() ;
        this.levelParams.remove(nextBoundSymbol) ;
        this.allParams.remove(nextBoundSymbol) ;
        this.nonLeibnizParams.remove(nextBoundSymbol) ;
       } ;


      /*********************************************************************
      * Compute this.levelConstraints.                                     *
      *********************************************************************/
      this.levelConstraints.putAll(opDef.getLevelConstraints());
      for (int i = 0; i < this.operands.length; i++) {
        if (this.operands[i] != null) {
          if (allBoundSymbols.size() == 0) {
              this.levelConstraints.putAll(
                 this.operands[i].getLevelConstraints());
           }
          else {
            /***************************************************************
            * There are bound identifiers, so we add a levelConstraint of  *
            * the operand to this.levelConstraints iff it is not a         *
            * constraint on a bound symbol.                                *
            *                                                              *
            * Note: this method of iterating over the elements of a        *
            * SetOfLevelConstraints copied from the toString() method in   *
            * SetOfLevelConstraints.java.                                  *
            ***************************************************************/
            SetOfLevelConstraints lcons =
               this.operands[i].getLevelConstraints() ;
            Iterator<SymbolNode> iter = lcons.keySet().iterator();
            while (iter.hasNext()) {
              SymbolNode param = iter.next() ;
              if (! allBoundSymbols.contains(param)) {
                this.levelConstraints.put(param, lcons.get(param)) ;
                }
             } // while
           } // else
        } // if (this.operands[i] != null)
      } // for i
      for (int i = 0; i < this.ranges.length; i++) {
        this.levelConstraints.putAll(this.ranges[i].getLevelConstraints());
      }
      for (int i = 0; i < this.operands.length; i++) {
        Integer mlevel = Integer.valueOf(opDef.getMaxLevel(i));
        if (this.operands[i] != null) {
          Iterator<SymbolNode> iter = this.operands[i].getLevelParams().iterator();
          while (iter.hasNext()) {
            this.levelConstraints.put(iter.next(), mlevel);
          }
        }
      }

      /*********************************************************************
      * Add to levelConstraints the ones introduced by this OpAppl to an   *
      * operator Op that appears as an operator argument.                  *
      *********************************************************************/
      for (int i = 0; i < this.operands.length; i++) {
        ExprOrOpArgNode opdi = this.operands[i];
        // LL changed OpDefNode -> AnyDefNode in the following.
        // See comments in AnyDefNode.java.  (It is only in the
        // most bizarre cases that opdi.getOp() would be a
        // ThmOrAssumpDefNode.
        if (opdi != null &&
            opdi instanceof OpArgNode &&
            ((OpArgNode)opdi).getOp() instanceof AnyDefNode) {
          AnyDefNode argDef = (AnyDefNode)((OpArgNode)opdi).getOp();
          argDef.levelCheck(itr) ;
            /***************************************************************
            * Need to invoke levelCheck before invoking getMaxLevel.       *
            ***************************************************************/
          int alen = argDef.getArity();
          for (int j = 0; j < this.operands.length; j++) {
            for (int k = 0; k < alen; k++) {
              if (opDef.getOpLevelCond(i, j, k)) {
                Integer mlevel = Integer.valueOf(argDef.getMaxLevel(k));
                Iterator<SymbolNode> iter = this.operands[j].getLevelParams().iterator();
                while (iter.hasNext()) {
                  this.levelConstraints.put(iter.next(), mlevel);
                }
              }
            }
          }; // forj
          /*****************************************************************
          * If argDef (the i-th operand, which is an OpDefNode) is not     *
          * Leibniz, then for each j and k for which opLevelCond[i][j][k]  *
          * = true, if argDef is not Leibniz in its k-th argument, then    *
          * every parameter in operands[j].allParams must be added to      *
          * this.nonLeibnizParams.  (See leibniz-checking.txt, appended    *
          * to LevelNode.java.)                                            *
          *****************************************************************/
          if (! argDef.getIsLeibniz()) {
            for (int j = 0; j < this.operands.length; j++) {
              for (int k = 0; k < alen; k++) {
                if (   opDef.getOpLevelCond(i, j, k)
                    && ! argDef.getIsLeibnizArg()[k]) {
                  this.nonLeibnizParams.addAll(this.operands[j].getAllParams()) ;
                } // if (opDef.getOpLevelCond(i, j, k))
               } // for k
             }; // forj
           } ; // if (! argDef.isLeibniz)
        } // if (opdi != null && ...)
      } // for i
      HashSet<ArgLevelParam> alpSet = opDef.getArgLevelParams();
      Iterator<ArgLevelParam> iter = alpSet.iterator();
      while (iter.hasNext()) {
        ArgLevelParam alp = iter.next();
        ExprOrOpArgNode arg = this.getArg(alp.op);
        // LL changed OpDefNode -> AnyDefNode in the following.
        // See comments in AnyDefNode.java.  (It is only in the
        // most bizarre cases that arg.getOp() would be a
        // ThmOrAssumpDefNode.
        if (arg != null &&
            arg instanceof OpArgNode &&
            ((OpArgNode)arg).getOp() instanceof AnyDefNode) {
          AnyDefNode argDef = (AnyDefNode)((OpArgNode)arg).getOp();
          argDef.levelCheck(itr) ;
            /***************************************************************
            * Need to invoke levelCheck before invoking getMaxLevel.       *
            ***************************************************************/
          Integer mlevel = Integer.valueOf(argDef.getMaxLevel(alp.i));
          this.levelConstraints.put(alp.param, mlevel);
        }
      } // while

//      this.argLevelConstraints = new SetOfArgLevelConstraints();
      /*********************************************************************
      * Compute this.argLevelConstraints.                                  *
      *********************************************************************/
      this.argLevelConstraints.putAll(opDef.getArgLevelConstraints());
      for (int i = 0; i < this.operands.length; i++) {
        if (this.operands[i] != null) {
          this.argLevelConstraints.putAll(
                         this.operands[i].getArgLevelConstraints());
        }
      }
      for (int i = 0; i < this.ranges.length; i++) {
        this.argLevelConstraints.putAll(this.ranges[i].getArgLevelConstraints());
      }
      for (int i = 0; i < this.operands.length; i++) {
        ExprOrOpArgNode opdi = this.operands[i];
        if (opdi != null &&
            opdi instanceof OpArgNode &&
            ((OpArgNode)opdi).getOp().isParam()) {
          SymbolNode opArg = ((OpArgNode)opdi).getOp();
          int alen = opArg.getArity();
          for (int j = 0; j < alen; j++) {
            ParamAndPosition pap = new ParamAndPosition(opArg, j);
            Integer mlevel = Integer.valueOf(opDef.getMinMaxLevel(i, j));
            this.argLevelConstraints.put(pap, mlevel);
          }
          for (int j = 0; j < this.operands.length; j++) {
            for (int k = 0; k < alen; k++) {
              if (opDef.getOpLevelCond(i, j, k)) {
                ParamAndPosition pap = new ParamAndPosition(opArg, k);
                Integer mlevel = Integer.valueOf(this.operands[j].getLevel());
                this.argLevelConstraints.put(pap, mlevel);
              }
            }
          }
        }
      } // for i
      iter = alpSet.iterator();
      while (iter.hasNext()) {
        ArgLevelParam alp = iter.next();
        ExprOrOpArgNode arg = this.getArg(alp.op);
        if (arg != null) {
          arg.levelCheck(itr) ;
            /***************************************************************
            * Have to invoke levelCheck before invoking getLevel.          *
            ***************************************************************/
          ParamAndPosition pap = new ParamAndPosition(alp.op, alp.i);
          this.argLevelConstraints.put(pap, Integer.valueOf(arg.getLevel()));
        }
      }

      /*********************************************************************
      * Compute this.argLevelParams.                                       *
      *********************************************************************/
      this.argLevelParams = new HashSet<>();
      for (int i = 0; i < this.operands.length; i++) {
        if (this.operands[i] != null) {
          if (allBoundSymbols.size() == 0) {
            this.argLevelParams.addAll(this.operands[i].getArgLevelParams());
           }
          else {
            /***************************************************************
            * There are bound identifiers, so we add an ArgLevelParam alp  *
            * of the operand to this.argLevelParams iff alp.param is not   *
            * a bound identifier.  For now at least, we will not add to    *
            * argLevelConstraints the element implied as described above   *
            * if alp.param IS a bound identifier.                          *
            ***************************************************************/
            Iterator<ArgLevelParam> alpIter = this.operands[i].getArgLevelParams().iterator();
            while (alpIter.hasNext()) {
              ArgLevelParam alp = alpIter.next() ;
              if (!allBoundSymbols.contains(alp.param)) {
                this.argLevelParams.add(alp) ;
               }
             } ;
           }
        }
      } ;
      for (int i = 0; i < this.ranges.length; i++) {
        this.argLevelParams.addAll(this.ranges[i].getArgLevelParams());
      } ;
      iter = alpSet.iterator();
      while (iter.hasNext()) {
        ArgLevelParam alp = (ArgLevelParam)iter.next();
        ExprOrOpArgNode arg = this.getArg(alp.op);
        if (arg == null) {
          arg = this.getArg(alp.param);
          if (arg == null) {
            this.argLevelParams.add(alp);
          }
          else {
            arg.levelCheck(itr) ;
              /*************************************************************
              * Need to invoke levelCheck before invoking getLevelParams.  *
              *************************************************************/
            Iterator<SymbolNode> iter1 = arg.getLevelParams().iterator();
            while (iter1.hasNext()) {
              SymbolNode param = iter1.next();
              this.argLevelParams.add(new ArgLevelParam(alp.op, alp.i, param));
            }
          }
        }
        else {
          if (arg instanceof OpArgNode &&
              ((OpArgNode)arg).getOp().isParam()) {
            SymbolNode argOp = ((OpArgNode)arg).getOp();
            this.argLevelParams.add(new ArgLevelParam(argOp, alp.i, alp.param));
          }
        }
      } // while
      /*********************************************************************
      * Add to argLevelParams the elements generated for operators that    *
      * appear as operator arguments.                                      *
      *********************************************************************/
      for (int i = 0; i < this.operands.length; i++) {
        ExprOrOpArgNode opdi = this.operands[i];
        if (opdi != null &&
            opdi instanceof OpArgNode &&
            ((OpArgNode)opdi).getOp().isParam()) {
          SymbolNode opArg = ((OpArgNode)opdi).getOp();
          int alen = opArg.getArity();
          for (int j = 0; j < this.operands.length; j++) {
            for (int k = 0; k < alen; k++) {
              if (opDef.getOpLevelCond(i, j, k)) {
                Iterator<SymbolNode> iter1 = this.operands[j].getLevelParams().iterator();
                while (iter1.hasNext()) {
                  SymbolNode param = iter1.next();
                  this.argLevelParams.add(new ArgLevelParam(opArg, k, param));
                }
              }
            }
          }
        }
      }
    } // if (this.operator instanceof OpDefNode)
    else {
      // Application of a declared operator
      this.operator.levelCheck(itr) ;
        /*******************************************************************
        * Need to invoke levelCheck before invoking getLevel.              *
        *******************************************************************/
      this.level = this.operator.getLevel();
      for (int i = 0; i < this.operands.length; i++) {
        this.operands[i].levelCheck(itr) ;
        this.level = Math.max(this.level, this.operands[i].getLevel());
      } // for

      this.levelParams = new HashSet<>();
      /*********************************************************************
      * We only add this.operator to the levelParams and allParams.        *
      *********************************************************************/
      this.levelParams.add(this.operator);
      this.allParams.add(this.operator);

      /*********************************************************************
      * Add to levelParams, allParams, and nonLeibnizParams the            *
      * corresponding parameters of the operands.                          *
      *********************************************************************/
      for (int i = 0; i < this.operands.length; i++) {
        this.levelParams.addAll(this.operands[i].getLevelParams());
        this.allParams.addAll(this.operands[i].getAllParams());
        this.nonLeibnizParams.addAll(this.operands[i].getNonLeibnizParams());
      }

      /*********************************************************************
      * Set levelConstraints to the union of the levelConstraints of the   *
      * operands.                                                          *
      *********************************************************************/
      this.levelConstraints = new SetOfLevelConstraints();
      for (int i = 0; i < this.operands.length; i++) {
        this.levelConstraints.putAll(this.operands[i].getLevelConstraints());
      }

      this.argLevelConstraints = new SetOfArgLevelConstraints();
      for (int i = 0; i < this.operands.length; i++) {
        /*******************************************************************
        * We add an argLevelConstraint for this.operator for it            *
        * indicating that it must allow its i-th argument to have          *
        * level at least the level of the i-th operand.                    *
        *******************************************************************/
        this.argLevelConstraints.put(this.operator,
                                         i, this.operands[i].getLevel());

        /*******************************************************************
        * We add to argLevelConstraints all the argLevelConstraints        *
        * coming from the i-th argument.                                   *
        *******************************************************************/
        this.argLevelConstraints.putAll(
           this.operands[i].getArgLevelConstraints());
      }

      this.argLevelParams = new HashSet<>();
      for (int i = 0; i < this.operands.length; i++) {
        /*******************************************************************
        * For every levelParam p of the i-th operand, add to               *
        * argLevelParams an entry asserting that p appears within an i-th  *
        * operand of this.operator.                                        *
        *******************************************************************/
        HashSet<SymbolNode> lpSet = this.operands[i].getLevelParams();
        Iterator<SymbolNode> iter = lpSet.iterator();
        while (iter.hasNext()) {
          SymbolNode param = iter.next();
          this.argLevelParams.add(
             new ArgLevelParam(this.operator, i, param));
         }; // end while

        /*******************************************************************
        * Add to argLevelParams all the argLevelParams entry for the i-th  *
        * operand.                                                         *
        *******************************************************************/
        this.argLevelParams.addAll(this.operands[i].getArgLevelParams());
       }; // end for
    }; // end else !(this.operator instanceof OpDefNode)

    /***********************************************************************
    * Check for the following illegal uses of temporal operators, where A  *
    * is an action-level formula.                                          *
    *                                                                      *
    *  - [] A where A is not [B]_v                                         *
    *                                                                      *
    *  - <> A where A is no <<B>>_v                                        *
    *                                                                      *
    *  - A ~> X or X ~> A                                                  *
    *                                                                      *
    *  - A -+-> X or X -+-> X                                              *
    *                                                                      *
    *  - \E or \A with a temporal-level body and an action-level bound.    *
    *    (Should this be an error with a state-level bound too?)           *
    *    Note that not a problem with CHOOSE, which does not allow a       *
    *    temporal body.                                                    *
    ***********************************************************************/
    String opName = this.operator.getName().toString();
    /***********************************************************************
    * Check for []A.                                                       *
    ***********************************************************************/
    if (opName.equals("[]")) {
      ExprNode arg = (ExprNode) this.getArgs()[0];
      if (  (arg.getLevel() == ActionLevel)
          && (arg.getKind() == OpApplKind)) {
        if (!((OpApplNode) arg).operator.getName().toString().equals(
                                                           "$SquareAct")) {
          errors.addError(
            stn.getLocation(),
            "[] followed by action not of form [A]_v.");
        }
      }
    };

    /***********************************************************************
    * Check for <>A.                                                       *
    ***********************************************************************/
    if (opName.equals("<>")) {
        ExprNode arg = (ExprNode) this.getArgs()[0];
        if (  (arg.getLevel() == ActionLevel)
            && (arg.getKind() == OpApplKind)) {
          if (!((OpApplNode) arg).operator.getName().toString().equals(
                                                             "$AngleAct")) {
            errors.addError(
              stn.getLocation(),
              "<> followed by action not of form <<A>>_v.");
          }
        }
      };

    /***********************************************************************
    * Check of ~> and -+->                                                 *
    ***********************************************************************/
    if (opName.equals("~>") || opName.equals("-+->")) {
      if (   (this.getArgs()[0].getLevel() == ActionLevel)
          || (this.getArgs()[1].getLevel() == ActionLevel)) {
          errors.addError(
             stn.getLocation(),
             "Action used where only temporal formula or " +
             "state predicate allowed.");
      }
    };

    /*
     * Check of logical operators /\ , \/ , => , <=>, and dis/conjunction
     * lists.  Added by LL 25 Oct 2013
     */
    if (   opName.equals("\\land")
    	|| opName.equals("\\lor")
    	|| opName.equals("=>")
    	|| opName.equals("\\equiv")
    	|| opName.equals("$ConjList")
    	|| opName.equals("$DisjList")) {
    	boolean hasTemporal = false ;
    	boolean hasAction = false ;
    	for (int i = 0; i < this.getArgs().length; i++) {
    		hasTemporal = hasTemporal || (this.getArgs()[i].getLevel() == TemporalLevel) ;
    		hasAction = hasAction || (this.getArgs()[i].getLevel() == ActionLevel) ;
    	}
    	if (hasTemporal && hasAction) {
    		String pop = opName ;
    		if (pop.equals("$ConjList")) {
    			pop = "Conjunction list" ;
    		}
    		if (pop.equals("$DisjList")) {
    			pop = "Disjunction list" ;
    		}
    		errors.addError(
    	             stn.getLocation(),
    	             pop + " has both temporal formula and action as arguments.");
    	}
    }

    /***********************************************************************
    * Check of \A and \E.                                                  *
    ***********************************************************************/
    if (    (this.level == TemporalLevel)
        && (   opName.equals("$BoundedExists")
            || opName.equals("$BoundedForall"))) {
      for (int i = 0; i < this.ranges.length; i++) {
          if (this.ranges[i].getLevel() == ActionLevel) {
              errors.addError(
                 this.ranges[i].stn.getLocation(),
                 "Action-level bound of quantified temporal formula.");
            }
          }

    }

    return this.levelCorrect;
  }

//  public final int getLevel() { return this.level; }
//
//  public final HashSet getLevelParams() { return this.levelParams; }
//
//  public final SetOfLevelConstraints getLevelConstraints() {
//    return this.levelConstraints;
//  }
//
//  public final SetOfArgLevelConstraints getArgLevelConstraints() {
//    return this.argLevelConstraints;
//  }
//
//  public final HashSet getArgLevelParams() { return this.argLevelParams; }

  /**
   * toString, levelDataToString, and walkGraph methods to implement
   * ExploreNode interface
   */
//  public final String levelDataToString() {
//    return "Level: "               + this.level               + "\n" +
//           "LevelParams: "         + this.levelParams         + "\n" +
//           "LevelConstraints: "    + this.levelConstraints    + "\n" +
//           "ArgLevelConstraints: " + this.argLevelConstraints + "\n" +
//           "ArgLevelParams: "      + this.argLevelParams      + "\n" ;
//  }


  public boolean hasOpcode(final int opCode) {
      return opCode == BuiltInOPs.getOpCode(getOperator().getName());
  }

  @Override
  public SemanticNode[] getChildren() {
      SemanticNode[] res =
         new SemanticNode[this.ranges.length + this.operands.length];
      int i;
      for (i = 0; i < this.ranges.length; i++) {
          res[i] = this.ranges[i];
      }
      for (int j = 0; j < this.operands.length; j++) {
          res[i+j] = this.operands[j];
      }
      return res;
   }

  /**
   * walkGraph finds all reachable nodes in the semantic graph
   * and inserts them in the Hashtable semNodesTable for use by the Explorer tool.
   */
  @Override
  public void walkGraph(Hashtable<Integer, ExploreNode> semNodesTable, ExplorerVisitor visitor) {
    Integer uid = Integer.valueOf(myUID);
    if (semNodesTable.get(uid) != null) return;

    semNodesTable.put(uid, this);
    visitor.preVisit(this);

    if (operator != null) {
      operator.walkGraph(semNodesTable, visitor);
    }

    if (unboundedBoundSymbols != null && unboundedBoundSymbols.length > 0) {
      for (int i = 0; i < unboundedBoundSymbols.length; i++)
        if (unboundedBoundSymbols[i] != null)
           unboundedBoundSymbols[i].walkGraph(semNodesTable, visitor);
    }

    if (operands != null && operands.length > 0) {
      for (int i = 0; i < operands.length; i++)
        if (operands[i] != null) operands[i].walkGraph(semNodesTable, visitor);
    }

    if (ranges.length > 0) {
      for (int i = 0; i < ranges.length; i++)
        if (ranges[i] != null) ranges[i].walkGraph(semNodesTable, visitor);
    }

    if (boundedBoundSymbols != null && boundedBoundSymbols.length > 0) {
      for (int i = 0; i < boundedBoundSymbols.length; i++) {
        if (boundedBoundSymbols[i] != null && boundedBoundSymbols[i].length > 0) {
          for (int j = 0; j < boundedBoundSymbols[i].length; j++) {
            if (boundedBoundSymbols[i][j] != null)
               boundedBoundSymbols[i][j].walkGraph(semNodesTable, visitor);
          }
        }
      }
    }
    visitor.postVisit(this);
  }

  // Used in implementation of toString() below
  private String toStringBody(int depth) {
    if (depth <= 1) return "";

    String ret;
    if (operator == null) {
      ret = "\nOperator: null";
    }
    else {
      ret = "\nOperator: " + operator.getName().toString() + "  "
            + operator.getUid() + "  ";
    }

    if (unboundedBoundSymbols!=null && unboundedBoundSymbols.length > 0) {
      ret += "\nUnbounded bound symbols:  ";
      for (int i = 0; i < unboundedBoundSymbols.length; i++) {
        ret += Strings.indent(2,unboundedBoundSymbols[i].toString(depth-1));
      }
    }

    if (boundedBoundSymbols != null && boundedBoundSymbols.length > 0) {
      ret += "\nBounded bound symbols: " + getNumberOfBoundedBoundSymbols();
      for (int i = 0; i < boundedBoundSymbols.length; i++) {
        if (boundedBoundSymbols[i] != null && boundedBoundSymbols[i].length > 0) {
          for (int j = 0; j < boundedBoundSymbols[i].length; j++) {
            ret += Strings.indent(2, "\n[" + i + "," + j + "]" +
                      Strings.indent(2,boundedBoundSymbols[i][j].toString(depth-1)));
          }
        }
      }
    }

    if (ranges.length > 0) {
      ret += "\nRanges: ";
      for (int i = 0; i < ranges.length; i++)
        ret += Strings.indent(2,(ranges[i] != null ?
                                     ranges[i].toString(depth-1) : "null" ));
    }

    if (tupleOrs != null && tupleOrs.length > 0 /* && tupleOrs[0] */) {
      ret += "\nTupleOrs:   ";
      for (int i = 0; i < tupleOrs.length; i++) {
        ret += Strings.indent(2, (tupleOrs[i] ? "\ntrue" : "\nfalse"));
      }
    }

    if (operands != null) {
      if (operands.length > 0) {
        ret += "\nOperands: " + operands.length;
        for (int i = 0; i < operands.length; i++) {
          ret += Strings.indent(2,
                    (operands[i] == null ? "\nnull" : operands[i].toString(depth-1)));
        }
      }
    }
    else {
      ret += "\nOperands: null";
    }
    return Strings.indent(2, ret);
  }

  /**
   * Displays this node as a String, implementing ExploreNode interface; depth
   * parameter is a bound on the depth of the portion of the tree that is displayed.
   */
  @Override
  public String toString(int depth) {
    if (depth <= 0) return "";
    String sEO = "" ;
    if (this.subExpressionOf != null) {
     sEO = Strings.indent(2,
              "\nsubExpressionOf: " +
              Strings.indent(2, this.subExpressionOf.toString(1))) ;} ;
    return "\n*OpApplNode: " + operator.getName() + "  " + super.toString(depth+1)
           + "  errors: " + (errors != null ? "non-null" : "null")
           + toStringBody(depth) + sEO ;
  }

    @Override
	public String toString(final IValue aValue) {
		if (aValue instanceof ITupleValue && allParams.size() == ((ITupleValue) aValue).size()) {
			final StringBuffer result = new StringBuffer();
			
			// The values in aValue are ordered by the varloc of the variable names (see
			// tlc2.tool.TLCStateMut.bind(UniqueString, Value, SemanticNode). Thus, sort
			// allParams - which are unordered - under same varloc order.
			final TreeSet<SymbolNode> s = new TreeSet<SymbolNode>(new java.util.Comparator<SymbolNode>() {
				@Override
				public int compare(SymbolNode o1, SymbolNode o2) {
					return Integer.compare(o1.getName().getVarLoc(), o2.getName().getVarLoc());
				}
			});
			s.addAll(allParams);
			
			int idx = 0;
			for (final SymbolNode sn : s) {
				result.append("/\\ ");
				result.append(sn.getName().toString());

				final IValue value = ((ITupleValue) aValue).getElem(idx++);
				result.append(" = ");
				result.append(Values.ppr(value));
				result.append("\n");
			}
			return result.toString();
		}
		return super.toString(aValue);
	}
  
  @Override
  protected Element getLevelElement(Document doc, SymbolContext context) {
    Element e = doc.createElement("OpApplNode");

    // TL 2014 - A fix for detecting null representing OTHER inside a case (please refrain from using null as a semantical object),
    // its form is
    // OpApplNode: Operator: $Case - Operands: 3(_,_,OpApplNode: Operator: $Pair - Operands: 2(null,_))
    if (operator.getName().toString().equals("$Case") && operands.length > 1 /* OTHER cannot occur alone in a CASE */) {
      // OTHER should be last operand
       ExprOrOpArgNode lastOperand = operands[operands.length-1];
       if (lastOperand instanceof tla2sany.semantic.OpApplNode) {
          OpApplNode other = (OpApplNode)lastOperand;
          // indeed the OTHER case
          if (other.getOperator().getName().toString().equals("$Pair") && other.getArgs()[0] == null) {
            // we pass a flag that tells any future OpApplNode that a null operand in 0 position should be replaced by the string $Other
            context = new SymbolContext(context);
            context.setFlag(SymbolContext.OTHER_BUG);
          }
       }

    }

    // operator
    Element op = doc.createElement("operator");
    op.appendChild(operator.export(doc,context));
    e.appendChild(op);

    // operands
    Element ope = doc.createElement("operands");
    for (int i=0; i< operands.length; i++) {
      // dealing with the $Case OTHER null bug
      if (i == 0 && operands[0] == null && context.hasFlag(SymbolContext.OTHER_BUG)) {
        ope.appendChild(appendText(doc,"StringNode","$Other"));
      }
      else {
        ope.appendChild(operands[i].export(doc,context));
      }
    }
    e.appendChild(ope);

    // bound variables (optional)
    if (unboundedBoundSymbols != null | boundedBoundSymbols != null ) {
      Element bvars = doc.createElement("boundSymbols");
      if (unboundedBoundSymbols != null) {
        for (int i=0; i< unboundedBoundSymbols.length; i++) {
          Element bvar = doc.createElement("unbound");
          bvar.appendChild(unboundedBoundSymbols[i].export(doc,context));
          if (tupleOrs != null && tupleOrs[i]) bvar.appendChild(doc.createElement("tuple"));
          bvars.appendChild(bvar);
        }
      }

      if (boundedBoundSymbols != null) {
        for (int i=0; i< boundedBoundSymbols.length; i++) {
          Element bvar = doc.createElement("bound");
          for (int j=0; j<boundedBoundSymbols[i].length; j++)
            bvar.appendChild(boundedBoundSymbols[i][j].export(doc,context));
          if (tupleOrs != null && tupleOrs[i]) bvar.appendChild(doc.createElement("tuple"));
          bvar.appendChild(ranges[i].export(doc,context));
          bvars.appendChild(bvar);
        }
      }
      e.appendChild(bvars);
    }

    return e;
  }
}
