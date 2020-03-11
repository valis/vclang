package org.arend.typechecking.termination;

import org.arend.core.context.param.DependentLink;
import org.arend.core.definition.Definition;
import org.arend.core.definition.FunctionDefinition;
import org.arend.core.elimtree.Body;
import org.arend.core.elimtree.ElimClause;
import org.arend.core.elimtree.IntervalElim;
import org.arend.core.expr.*;
import org.arend.core.pattern.*;
import org.arend.prelude.Prelude;
import org.arend.typechecking.visitor.ProcessDefCallsVisitor;
import org.arend.util.Pair;

import java.util.*;

public class CollectCallVisitor extends ProcessDefCallsVisitor<Void> {
    private final Set<BaseCallMatrix<Definition>> myCollectedCalls;
    private final FunctionDefinition myDefinition;
    private final Set<? extends Definition> myCycle;
    private List<? extends ExpressionPattern> myVector;

    CollectCallVisitor(FunctionDefinition def, Set<? extends Definition> cycle) {
        assert cycle != null;
        myDefinition = def;
        myCycle = cycle;
        myCollectedCalls = new HashSet<>();

        collectIntervals();
    }

    private void collectIntervals() {
        Body body = myDefinition.getActualBody();
        if (body instanceof IntervalElim) {
            IntervalElim elim = (IntervalElim) body;
            List<ExpressionPattern> vector = new ArrayList<>();
            for (DependentLink link = myDefinition.getParameters(); link.hasNext(); link = link.getNext()) {
                vector.add(new BindingPattern(link));
            }

            myVector = vector;
            int i = vector.size() - elim.getCases().size();

            for (Pair<Expression, Expression> pair : elim.getCases()) {
                ExpressionPattern old = vector.get(i);
                vector.set(i, new ConstructorExpressionPattern(ExpressionFactory.Left(), Collections.emptyList()));
                pair.proj1.accept(this, null);
                vector.set(i, new ConstructorExpressionPattern(ExpressionFactory.Right(), Collections.emptyList()));
                pair.proj2.accept(this, null);
                vector.set(i, old);
            }
        }

        Expression resultType = myDefinition.getResultType();
        if (resultType != null) {
            List<ExpressionPattern> vector = new ArrayList<>();

            for (DependentLink p = myDefinition.getParameters(); p.hasNext(); p = p.getNext()) {
                p = p.getNextTyped(null);
                vector.add(new BindingPattern(p));
            }

            myVector = vector;
            resultType.accept(this, null);
        }
    }

    public void collect(ElimClause<ExpressionPattern> clause) {
        if (clause.getExpression() != null) {
            myVector = clause.getPatterns();
            clause.getExpression().accept(this, null);
        }
    }

    public Set<BaseCallMatrix<Definition>> getResult() {
        return myCollectedCalls;
    }

    private static BaseCallMatrix.R isLess(Expression expr1, ExpressionPattern pattern2) {
        if (pattern2 instanceof ConstructorExpressionPattern) {
            ConstructorExpressionPattern conPattern = (ConstructorExpressionPattern) pattern2;

            List<? extends Expression> exprArguments = conPattern.getMatchingExpressionArguments(expr1, false);
            if (exprArguments != null) {
                List<? extends ExpressionPattern> cpSubpatterns = conPattern.getSubPatterns();
                for (int i = 0; i < Math.min(exprArguments.size(), cpSubpatterns.size()); i++) {
                    BaseCallMatrix.R ord = isLess(exprArguments.get(i), cpSubpatterns.get(i));
                    if (ord != BaseCallMatrix.R.Equal) return ord;
                }

                if (exprArguments.size() >= cpSubpatterns.size()) return BaseCallMatrix.R.Equal;
                return BaseCallMatrix.R.Unknown;
            }

            for (ExpressionPattern arg : conPattern.getSubPatterns()) {
                if (isLess(expr1, arg) != BaseCallMatrix.R.Unknown) return BaseCallMatrix.R.LessThan;
            }
            return BaseCallMatrix.R.Unknown;
        } else if (pattern2 instanceof BindingPattern) {
            DependentLink binding2 = ((BindingPattern) pattern2).getBinding();
            if (expr1 instanceof ReferenceExpression) {
                if (((ReferenceExpression) expr1).getBinding() == binding2) return BaseCallMatrix.R.Equal;
            } else if (expr1 instanceof AppExpression) {
                Expression function = expr1.getFunction();
                if (function instanceof ReferenceExpression && ((ReferenceExpression) function).getBinding() == binding2)
                    return BaseCallMatrix.R.LessThan; // ensures that "e x < e"
            }
        }
        return BaseCallMatrix.R.Unknown;
    }

    private static void initMatrixBlock(CallMatrix callMatrix,
                                        Expression expr1, DependentLink param1,
                                        ExpressionPattern pattern2, DependentLink param2) {
        //param1 and param2 should be used to designate subblocks of the call matrix
        if (pattern2 instanceof ConstructorExpressionPattern) {
            ConstructorExpressionPattern conPattern = (ConstructorExpressionPattern) pattern2;

            List<? extends Expression> exprArguments = conPattern.getMatchingExpressionArguments(expr1, false);
            if (exprArguments != null) {
                List<? extends ExpressionPattern> cpSubpatterns = conPattern.getSubPatterns();
                DependentLink param1u = CallMatrix.unfoldSigmaType(param1);
                DependentLink param2u = CallMatrix.unfoldSigmaType(param2);
                if (param1u != null && param2u != null) {
                    doProcessLists(callMatrix, param2u, cpSubpatterns, param1u, exprArguments);
                    return;
                }

            }
        }
        callMatrix.setBlock(param2, param1, isLess(expr1, pattern2));
    }

    private static void doProcessLists(CallMatrix cm, DependentLink rangePattern, List<? extends ExpressionPattern> myVector, DependentLink rangeArgument, List<? extends Expression> defCallArguments) {
        for (ExpressionPattern pattern : myVector) {
            DependentLink rangeArg = rangeArgument;
            for (Expression argument : defCallArguments) {
                // strip currentExpression of App & Proj calls
                while (true) {
                    if (argument instanceof AppExpression) {
                        argument = argument.getFunction();
                    } else if (argument instanceof ProjExpression) {
                        argument = ((ProjExpression) argument).getExpression();
                    } else if (argument instanceof FunCallExpression && ((FunCallExpression) argument).getDefinition() == Prelude.AT) {
                        argument = ((FunCallExpression) argument).getDefCallArguments().get(3);
                    } else {
                        break;
                    }
                }
                initMatrixBlock(cm, argument, rangeArg, pattern, rangePattern);
                rangeArg = rangeArg.getNext();
            }
            rangePattern = rangePattern.getNext();
        }
    }

    @Override
    protected boolean processDefCall(DefCallExpression expression, Void param) {
        if (!myCycle.contains(expression.getDefinition())) {
            return false;
        }

        CallMatrix cm = new CallMatrix(myDefinition, expression);
        doProcessLists(cm, myDefinition.getParameters(), myVector,
                expression.getDefinition().getParameters(), expression.getDefCallArguments());

        myCollectedCalls.add(cm);
        return false;
    }
}
