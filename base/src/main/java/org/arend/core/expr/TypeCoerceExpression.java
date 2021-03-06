package org.arend.core.expr;

import org.arend.core.context.param.DependentLink;
import org.arend.core.definition.FunctionDefinition;
import org.arend.core.elimtree.Body;
import org.arend.core.elimtree.ElimBody;
import org.arend.core.elimtree.ElimClause;
import org.arend.core.expr.visitor.ExpressionVisitor;
import org.arend.core.expr.visitor.ExpressionVisitor2;
import org.arend.core.pattern.ExpressionPattern;
import org.arend.core.pattern.Pattern;
import org.arend.core.subst.ExprSubstitution;
import org.arend.core.subst.LevelPair;
import org.arend.core.subst.LevelSubstitution;
import org.arend.ext.core.definition.CoreFunctionDefinition;
import org.arend.ext.core.expr.CoreExpressionVisitor;
import org.arend.ext.core.expr.CoreTypeCoerceExpression;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.util.Decision;
import org.jetbrains.annotations.NotNull;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

public class TypeCoerceExpression extends Expression implements CoreTypeCoerceExpression {
  private final FunctionDefinition myDefinition;
  private LevelPair myLevels;
  private final int myClauseIndex;
  private final List<Expression> myClauseArguments;
  private Expression myArgument;
  private final boolean myFromLeftToRight;

  private TypeCoerceExpression(FunctionDefinition definition, LevelPair levels, int clauseIndex, List<Expression> clauseArguments, Expression argument, boolean fromLeftToRight) {
    myDefinition = definition;
    myLevels = levels;
    myClauseIndex = clauseIndex;
    myClauseArguments = clauseArguments;
    myArgument = argument;
    myFromLeftToRight = fromLeftToRight;
  }

  public static Expression make(FunctionDefinition definition, LevelPair levels, int clauseIndex, List<Expression> clauseArguments, Expression argument, boolean fromLeftToRight) {
    TypeCoerceExpression typeCoerce = argument == null ? null : argument.cast(TypeCoerceExpression.class);
    return typeCoerce != null && definition == typeCoerce.myDefinition && fromLeftToRight != typeCoerce.myFromLeftToRight ? typeCoerce.myArgument : new TypeCoerceExpression(definition, levels, clauseIndex, clauseArguments, argument, fromLeftToRight);
  }

  public static Expression match(FunCallExpression funCall, Expression argument, boolean fromLeftToRight) {
    if (funCall.getDefinition().getKind() != CoreFunctionDefinition.Kind.TYPE) return null;
    if (funCall.getDefinition().getActualBody() instanceof Expression) {
      return TypeCoerceExpression.make(funCall.getDefinition(), funCall.getLevels(), -1, new ArrayList<>(funCall.getDefCallArguments()), argument, fromLeftToRight);
    }
    if (!(funCall.getDefinition().getActualBody() instanceof ElimBody)) return null;

    List<? extends ElimClause<Pattern>> clauses = ((ElimBody) funCall.getDefinition().getActualBody()).getClauses();
    for (int i = 0; i < clauses.size(); i++) {
      List<Expression> result = new ArrayList<>();
      List<ExpressionPattern> patterns = Pattern.toExpressionPatterns(clauses.get(i).getPatterns(), funCall.getDefinition().getParameters());
      if (patterns == null) continue;
      if (ExpressionPattern.match(patterns, funCall.getDefCallArguments(), result) == Decision.YES) {
        return TypeCoerceExpression.make(funCall.getDefinition(), funCall.getLevels(), i, result, argument, fromLeftToRight);
      }
    }

    return null;
  }

  public static Expression unfoldType(Expression type) {
    type = type.normalize(NormalizationMode.WHNF);
    while (type instanceof FunCallExpression && ((FunCallExpression) type).getDefinition().getKind() == CoreFunctionDefinition.Kind.TYPE) {
      Expression next = TypeCoerceExpression.match((FunCallExpression) type, null, false);
      if (next == null) return type;
      type = ((TypeCoerceExpression) next).getRHSType().normalize(NormalizationMode.WHNF);
    }
    return type;
  }

  public static Expression unfoldExpression(Expression expr) {
    expr = expr.normalize(NormalizationMode.WHNF);
    while (expr instanceof TypeCoerceExpression && !((TypeCoerceExpression) expr).isFromLeftToRight()) {
      expr = ((TypeCoerceExpression) expr).getArgument().normalize(NormalizationMode.WHNF);
    }
    return expr;
  }

  public Expression getArgumentType() {
    return myFromLeftToRight ? getLHSType() : getRHSType();
  }

  @Override
  public Expression getType() {
    return myFromLeftToRight ? getRHSType() : getLHSType();
  }

  @Override
  public @NotNull FunCallExpression getLHSType() {
    Body body = myDefinition.getActualBody();
    if (body instanceof Expression) {
      return FunCallExpression.makeFunCall(myDefinition, myLevels, myClauseArguments);
    } else {
      ElimClause<Pattern> clause = ((ElimBody) Objects.requireNonNull(body)).getClauses().get(myClauseIndex);
      List<ExpressionPattern> patterns = Pattern.toExpressionPatterns(clause.getPatterns(), myDefinition.getParameters());
      List<Expression> defCallArguments = ExpressionPattern.applyClauseArguments(patterns, myClauseArguments, myLevels);
      return FunCallExpression.makeFunCall(myDefinition, myLevels, defCallArguments);
    }
  }

  @Override
  public @NotNull Expression getRHSType() {
    Body body = myDefinition.getActualBody();
    if (body instanceof Expression) {
      return ((Expression) body).subst(new ExprSubstitution().add(myDefinition.getParameters(), myClauseArguments), myLevels);
    } else {
      ElimClause<Pattern> clause = ((ElimBody) Objects.requireNonNull(body)).getClauses().get(myClauseIndex);
      return Objects.requireNonNull(clause.getExpression()).subst(new ExprSubstitution().add(Pattern.getFirstBinding(clause.getPatterns()), myClauseArguments), myLevels);
    }
  }

  public FunctionDefinition getDefinition() {
    return myDefinition;
  }

  public LevelPair getLevels() {
    return myLevels;
  }

  public void substSort(LevelSubstitution substitution) {
    myLevels = myLevels.subst(substitution);
  }

  public int getClauseIndex() {
    return myClauseIndex;
  }

  public List<Expression> getClauseArguments() {
    return myClauseArguments;
  }

  public DependentLink getParameters() {
    return myDefinition.getActualBody() instanceof ElimBody ? Pattern.getFirstBinding(((ElimBody) myDefinition.getActualBody()).getClauses().get(myClauseIndex).getPatterns()) : myDefinition.getParameters();
  }

  @Override
  public @NotNull Expression getArgument() {
    return myArgument;
  }

  public void setArgument(Expression argument) {
    myArgument = argument;
  }

  @Override
  public boolean isFromLeftToRight() {
    return myFromLeftToRight;
  }

  @Override
  public <P, R> R accept(@NotNull CoreExpressionVisitor<? super P, ? extends R> visitor, P params) {
    return visitor.visitTypeCoerce(this, params);
  }

  @Override
  public <P, R> R accept(ExpressionVisitor<? super P, ? extends R> visitor, P params) {
    return visitor.visitTypeCoerce(this, params);
  }

  @Override
  public <P1, P2, R> R accept(ExpressionVisitor2<? super P1, ? super P2, ? extends R> visitor, P1 param1, P2 param2) {
    return visitor.visitTypeCoerce(this, param1, param2);
  }

  @Override
  public Decision isWHNF() {
    TypeCoerceExpression other = myArgument.cast(TypeCoerceExpression.class);
    if (other != null && other.myFromLeftToRight != myFromLeftToRight) return Decision.NO;
    return myArgument.isWHNF();
  }

  @Override
  public Expression getStuckExpression() {
    TypeCoerceExpression other = myArgument.cast(TypeCoerceExpression.class);
    return other != null && other.myFromLeftToRight != myFromLeftToRight ? null : myArgument.getStuckExpression();
  }
}
