package org.notmysock.hive.hooks;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;
import java.util.Set;
import java.util.TreeSet;

import org.apache.commons.logging.Log;
import org.apache.commons.logging.LogFactory;
import org.apache.hadoop.hive.ql.exec.FilterOperator;
import org.apache.hadoop.hive.ql.exec.FunctionRegistry;
import org.apache.hadoop.hive.ql.exec.Operator;
import org.apache.hadoop.hive.ql.exec.TableScanOperator;
import org.apache.hadoop.hive.ql.exec.Task;
import org.apache.hadoop.hive.ql.lib.Node;
import org.apache.hadoop.hive.ql.parse.ASTNode;
import org.apache.hadoop.hive.ql.parse.AbstractSemanticAnalyzerHook;
import org.apache.hadoop.hive.ql.parse.HiveSemanticAnalyzerHookContext;
import org.apache.hadoop.hive.ql.parse.SemanticException;
import org.apache.hadoop.hive.ql.plan.ExprNodeColumnDesc;
import org.apache.hadoop.hive.ql.plan.ExprNodeConstantDesc;
import org.apache.hadoop.hive.ql.plan.ExprNodeDesc;
import org.apache.hadoop.hive.ql.plan.ExprNodeDesc.ExprNodeDescEqualityWrapper;
import org.apache.hadoop.hive.ql.plan.ExprNodeDescUtils;
import org.apache.hadoop.hive.ql.plan.ExprNodeGenericFuncDesc;
import org.apache.hadoop.hive.ql.plan.MapWork;
import org.apache.hadoop.hive.ql.plan.api.OperatorType;
import org.apache.hadoop.hive.ql.udf.generic.GenericUDF;
import org.apache.hadoop.hive.ql.udf.generic.GenericUDFIn;
import org.apache.hadoop.hive.ql.udf.generic.GenericUDFOPAnd;
import org.apache.hadoop.hive.ql.udf.generic.GenericUDFOPEqual;
import org.apache.hadoop.hive.ql.udf.generic.GenericUDFOPOr;
import org.apache.hadoop.hive.serde2.objectinspector.ObjectInspector;
import org.apache.hadoop.hive.serde2.objectinspector.ObjectInspectorConverters;
import org.apache.hadoop.hive.serde2.objectinspector.ObjectInspector.Category;
import org.apache.hadoop.hive.serde2.objectinspector.ObjectInspectorConverters.Converter;
import org.apache.hadoop.hive.serde2.objectinspector.ObjectInspectorFactory;
import org.apache.hadoop.hive.serde2.objectinspector.PrimitiveObjectInspector;
import org.apache.hadoop.hive.serde2.objectinspector.PrimitiveObjectInspector.PrimitiveCategory;
import org.apache.hadoop.hive.serde2.typeinfo.PrimitiveTypeInfo;
import org.apache.hadoop.hive.serde2.typeinfo.TypeInfo;
import org.apache.hadoop.hive.serde2.typeinfo.TypeInfoFactory;
import org.apache.hadoop.hive.serde2.typeinfo.TypeInfoUtils;
import org.datanucleus.store.rdbms.sql.expression.ExpressionUtils;

import com.google.common.base.Preconditions;
import com.google.common.collect.Lists;

public class AndOrRewriteHook extends AbstractSemanticAnalyzerHook {
	protected static final Log LOG = LogFactory.getLog(AndOrRewriteHook.class
			.getName());
	
	@Override
	public void postAnalyze(HiveSemanticAnalyzerHookContext context,
			List<Task<? extends Serializable>> rootTasks)
			throws SemanticException {
		if (rootTasks == null || rootTasks.size() != 1) {
			return;
		}
		Collection<MapWork> work = rootTasks.get(0).getMapWork();
		if (work == null || work.size() != 1) {
			return;
		}
		for (MapWork w : work) {
			Set<Operator<?>> ops = w.getAllRootOperators();
			for(Operator p : ops) {
				//Optimization criteria - TS followed by FIL 
				if (p.getType() == OperatorType.TABLESCAN) {
					List<Operator> children = p.getChildOperators();
					LOG.info("GOPAL : " + children);
					if (children != null && children.size() == 1) {
						Operator first = children.get(0);
						if (first.getType() == OperatorType.FILTER) {
							processTableFilter((TableScanOperator)p, (FilterOperator)first);
						}
					} else {
						break;
					}
				}
			}
		}
	}

	private void processTableFilter(TableScanOperator ts, FilterOperator fil) {
		LOG.info("GOPAL: Great Success");
		// for an OR tree, gather into an ANY
		ExprNodeDesc predicate = fil.getConf().getPredicate();
		Queue<ExprNodeDesc> queue = new LinkedList<ExprNodeDesc>();
		List<ExprNodeDesc> any = new ArrayList<ExprNodeDesc>();
		queue.add(predicate);
		while (!queue.isEmpty()) {
			ExprNodeDesc inner = queue.remove();
			if (inner instanceof ExprNodeGenericFuncDesc) {
				final ExprNodeGenericFuncDesc genFunc = (ExprNodeGenericFuncDesc) inner;
				final GenericUDF udf = genFunc.getGenericUDF();
				if (udf instanceof GenericUDFOPOr) {
					queue.addAll(genFunc.getChildren());
				} else {
					any.add(inner);
				}
			} else {
				any.add(inner);
			}
		}
		if (any.size() < 7) {
			// no value
			return;
		}
		GenericUDF first = null;
		for (ExprNodeDesc inner : any) {
			if(inner instanceof ExprNodeGenericFuncDesc) {
				final ExprNodeGenericFuncDesc genFunc = (ExprNodeGenericFuncDesc) inner;
				final GenericUDF udf = genFunc.getGenericUDF();
				if (first == null) {
					first = udf;
				} else {
					if (!first.getClass().equals(udf.getClass())) {
						LOG.info("The inner ANY clauses are not uniform : " + first + " ~~> " + udf);
						return;
					}
				}
			} else {
				LOG.info("The inner ANY clauses are not functions: " + inner);
				return;
			}
		}
		
		// all parts of ANY are the same UDF type as first
		LOG.info("We have " + any.size() + " instances of " + first);
		
		if (FunctionRegistry.isStateful(first) == false
				&& FunctionRegistry.isDeterministic(first) == false) {
			LOG.info(" Turns out " + first + " is non-deterministic. Exiting");
		}
		
		final List<ExprNodeDesc> subexpr;
		
		if (first instanceof GenericUDFOPAnd) {
			subexpr = decomposeAndPredicates(any);
		} else {
			subexpr = null;
		}

		ExprNodeDesc finalPredicate = balanceAnyPredicates(any);
		fil.getConf().setPredicate(finalPredicate);
	}

	private ExprNodeDesc balanceAnyPredicates(List<ExprNodeDesc> any) {
		// turn ANY expr node desc list into a balanced tree
		
		Queue<ExprNodeDesc> queue = new LinkedList<ExprNodeDesc>();
		queue.addAll(any);
		while (!queue.isEmpty()) {
			ExprNodeDesc first = queue.remove();
			ExprNodeDesc second = queue.poll();
			if (second != null) {
				GenericUDFOPOr or = new GenericUDFOPOr();
				List<ExprNodeDesc> expressions = new ArrayList<ExprNodeDesc>(2);
				expressions.add(first);
				expressions.add(second);
				ExprNodeDesc orExpr = new ExprNodeGenericFuncDesc(
						TypeInfoFactory.booleanTypeInfo, or, expressions);
				queue.add(orExpr);
			} else {
				return first;
			}
		}
		Preconditions.checkArgument(false, "This is a trap!");
		return null;
	}
	
	private ExprNodeDesc balanceAllPredicates(List<ExprNodeDesc> all) {
		// turn ALL expr node desc list into a balanced tree
		
		Queue<ExprNodeDesc> queue = new LinkedList<ExprNodeDesc>();
		queue.addAll(all);
		while (!queue.isEmpty()) {
			ExprNodeDesc first = queue.remove();
			ExprNodeDesc second = queue.poll();
			if (second != null) {
				GenericUDFOPAnd and = new GenericUDFOPAnd();
				List<ExprNodeDesc> expressions = new ArrayList<ExprNodeDesc>(2);
				expressions.add(first);
				expressions.add(second);
				ExprNodeDesc andExpr = new ExprNodeGenericFuncDesc(
						TypeInfoFactory.booleanTypeInfo, and, expressions);
				queue.add(andExpr);
			} else {
				return first;
			}
		}
		Preconditions.checkArgument(false, "This is a trap!");
		return null;
	}

	private final class AndRange {
		final ExprNodeColumnDesc column;
		final Set<ExprNodeDescEqualityWrapper> constants = new HashSet<ExprNodeDescEqualityWrapper>();
		int items = 0;
		
		public AndRange(ExprNodeColumnDesc col) {
			this.column = col;
		}
		
		public void add(ExprNodeConstantDesc cons) {
			items++;
			LOG.info(column + " += " + cons.getExprString() + String.format(" [%d items, ndv %d]", items, cost()));
			constants.add(new ExprNodeDescEqualityWrapper(cons));
		}
		
		public ExprNodeDesc getExpr() {
			GenericUDFIn in = new GenericUDFIn();
			List<ExprNodeDesc> expressions = new ArrayList<ExprNodeDesc>(constants.size() + 1);
			// IN(col, ... constants)
			expressions.add(column);
			for (ExprNodeDescEqualityWrapper wrap : constants) {
				expressions.add(wrap.getExprNodeDesc());	
			}
			return new ExprNodeGenericFuncDesc(
					TypeInfoFactory.booleanTypeInfo, in, expressions);
		}
		
		public int cost() {
			return constants.size();
		}
	}
	
	private List<ExprNodeDesc> decomposeAndPredicates(List<ExprNodeDesc> any) {
		DefaultHashMap<ExprNodeDescEqualityWrapper, AndRange> expr = new DefaultHashMap<ExprNodeDescEqualityWrapper, AndRange>() {
			@Override
			public AndRange defaultValue(ExprNodeDescEqualityWrapper wrap) {
				ExprNodeColumnDesc key = (ExprNodeColumnDesc) wrap.getExprNodeDesc();
				if (key.getTypeInfo().getCategory() == Category.PRIMITIVE) {
					PrimitiveTypeInfo pti = (PrimitiveTypeInfo) key
							.getTypeInfo();
					return new AndRange(key);
				}
				return null;
			}
		};
		
		// generate a sub expression from a list of AND trees into ALL expressions
  		for (ExprNodeDesc and : any) {
  			// this is recursive, but we're ok with that
  			List<ExprNodeDesc> all = ExprNodeDescUtils.split(and);
  			boolean oneMatch = false; // at least one AND has to return a col = const to consider the optimization
  			for (ExprNodeDesc inner : all) {
  				final ExprNodeGenericFuncDesc genFunc = (ExprNodeGenericFuncDesc) inner;
				final GenericUDF udf = genFunc.getGenericUDF();
  				if (udf instanceof GenericUDFOPEqual) {
  					List<ExprNodeDesc> eq = genFunc.getChildren();
  					ExprNodeColumnDesc col = null;
  					ExprNodeConstantDesc cons = null;
  					for (ExprNodeDesc hs : eq) {
  						if (hs instanceof ExprNodeColumnDesc) {
  							col = (ExprNodeColumnDesc) hs;
  						} else if (hs instanceof ExprNodeConstantDesc) {
  							cons = (ExprNodeConstantDesc) hs;
  						} else {
  							LOG.info("Unexpected type in AND expr " + hs);
  						}
  					}
  					if (cons != null || col != null) {
  						AndRange range = expr.getDefault(new ExprNodeDescEqualityWrapper(col));
  						if (range != null) {
  							// we can't help unknown range types
  	  						oneMatch = true;
  	  						range.add(cons);
  						}
  					}
  				}
  			}
  			if (oneMatch != true) {
  				LOG.info("We can't fold the AND, due to " + and.getExprString());
  				return null;
  			}
		}
  		
  		ArrayList<AndRange> subExprs = new ArrayList<AndRange>();
		for (AndRange subExpr : expr.values()) {
			if (subExpr.cost() < 1024) {
				subExprs.add(subExpr);
			}
			LOG.info("GOPAL: " + subExpr.column + " has a cost of " + subExpr.cost() + " and " + subExpr.items);
		}
		
  		Collections.sort(subExprs, new Comparator<AndRange>() {
			@Override
			public int compare(AndRange o1, AndRange o2) {
				if (o1.cost() > o2.cost()) {
					return 1;
				} else if (o1.cost() < o2.cost()) {
					return -1;
				}
				return 0;
			}
  		});
  		
		return null;
	}
}
