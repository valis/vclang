package org.arend.typechecking.subexpr;

import org.arend.core.context.param.DependentLink;
import org.arend.core.definition.ClassDefinition;
import org.arend.core.definition.ClassField;
import org.arend.core.elimtree.ElimClause;
import org.arend.core.expr.*;
import org.arend.core.expr.let.HaveClause;
import org.arend.core.pattern.Pattern;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.typechecking.MetaDefinition;
import org.arend.naming.reference.GlobalReferable;
import org.arend.naming.reference.MetaReferable;
import org.arend.naming.reference.Referable;
import org.arend.prelude.Prelude;
import org.arend.term.concrete.Concrete;
import org.arend.term.concrete.ConcreteExpressionVisitor;
import org.arend.util.Pair;
import org.jetbrains.annotations.Contract;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.*;
import java.util.function.BiFunction;
import java.util.stream.Collectors;

public class CorrespondedSubExprVisitor implements
    ConcreteExpressionVisitor<@NotNull Expression,
        @Nullable Pair<@NotNull Expression, Concrete.@NotNull Expression>> {
  private final @NotNull Concrete.Expression subExpr;
  private final @NotNull List<@NotNull SubExprError> errors = new ArrayList<>();

  @Contract(pure = true)
  public @NotNull List<@NotNull SubExprError> getErrors() {
    return errors;
  }

  public CorrespondedSubExprVisitor(@NotNull Concrete.Expression subExpr) {
    this.subExpr = subExpr;
  }

  private boolean matchesSubExpr(@NotNull Concrete.Expression expr) {
    return Objects.equals(expr.getData(), subExpr.getData());
  }

  @Contract(value = "_->null")
  private @Nullable Pair<Expression, Concrete.Expression> nullWithError(@NotNull SubExprError error) {
    errors.add(error);
    return null;
  }

  @Contract(pure = true)
  private @Nullable Pair<Expression, Concrete.Expression> atomicExpr(@NotNull Concrete.Expression expr, @NotNull Expression coreExpr) {
    return matchesSubExpr(expr) ? new Pair<>(coreExpr, expr) : null;
  }

  @Override
  public Pair<Expression, Concrete.Expression> visitHole(Concrete.HoleExpression expr, Expression coreExpr) {
    return atomicExpr(expr, coreExpr);
  }

  @Override
  public Pair<Expression, Concrete.Expression> visitReference(Concrete.ReferenceExpression expr, Expression coreExpr) {
    if (matchesSubExpr(expr)) return new Pair<>(coreExpr, expr);
    Referable ref = expr.getReferent();
    if (ref instanceof MetaReferable) {
      MetaDefinition meta = ((MetaReferable) ref).getDefinition();
      if (meta != null) {
        ConcreteExpression concrete = meta.checkAndGetConcreteRepresentation(Collections.emptyList());
        if (concrete instanceof Concrete.Expression) {
          return ((Concrete.Expression) concrete).accept(this, coreExpr);
        }
      }
      return nullWithError(new SubExprError(SubExprError.Kind.MetaRef, coreExpr));
    }
    return null;
  }

  @Override
  public Pair<Expression, Concrete.Expression> visitThis(Concrete.ThisExpression expr, Expression coreExpr) {
    return atomicExpr(expr, coreExpr);
  }

  @Override
  public Pair<Expression, Concrete.Expression> visitApplyHole(Concrete.ApplyHoleExpression expr, Expression coreExpr) {
    return atomicExpr(expr, coreExpr);
  }

  @Override
  public Pair<Expression, Concrete.Expression> visitNumericLiteral(Concrete.NumericLiteral expr, Expression coreExpr) {
    return atomicExpr(expr, coreExpr);
  }

  @Override
  public @Nullable Pair<@NotNull Expression, Concrete.@NotNull Expression> visitStringLiteral(Concrete.StringLiteral expr, @NotNull Expression coreExpr) {
    return atomicExpr(expr, coreExpr);
  }

  @Override
  public Pair<Expression, Concrete.Expression> visitUniverse(Concrete.UniverseExpression expr, Expression coreExpr) {
    return atomicExpr(expr, coreExpr);
  }

  @Override
  public Pair<Expression, Concrete.Expression> visitGoal(Concrete.GoalExpression goalExpr, Expression coreGoalExpr) {
    if (coreGoalExpr instanceof GoalErrorExpression) {
      var innerConcreteExpression = goalExpr.expression;
      var innerCoreExpression = ((GoalErrorExpression) coreGoalExpr).getExpression();
      if (innerConcreteExpression != null && innerCoreExpression != null) {
        return innerConcreteExpression.accept(this, innerCoreExpression);
      }
    }
    return atomicExpr(goalExpr, coreGoalExpr);
  }

  @Override
  public Pair<Expression, Concrete.Expression> visitProj(Concrete.ProjExpression expr, Expression coreExpr) {
    if (matchesSubExpr(expr)) return new Pair<>(coreExpr, expr);
    var coreProjExpr = coreExpr.cast(ProjExpression.class);
    if (coreProjExpr == null) return nullWithError(SubExprError.mismatch(coreExpr));
    return expr.getExpression().accept(this, coreProjExpr.getExpression());
  }

  @Override
  public Pair<Expression, Concrete.Expression> visitNew(Concrete.NewExpression expr, Expression coreExpr) {
    if (matchesSubExpr(expr)) return new Pair<>(coreExpr, expr);
    var coreNewExpr = coreExpr.cast(NewExpression.class);
    if (coreNewExpr == null) return nullWithError(SubExprError.mismatch(coreExpr));
    return expr.getExpression().accept(this, coreNewExpr.getClassCall());
  }

  @Override
  public Pair<Expression, Concrete.Expression> visitTuple(Concrete.TupleExpression expr, Expression coreExpr) {
    if (matchesSubExpr(expr)) return new Pair<>(coreExpr, expr);
    var coreTupleExpr = coreExpr.cast(TupleExpression.class);
    if (coreTupleExpr == null) return nullWithError(SubExprError.mismatch(coreExpr));
    return visitExprs(coreTupleExpr.getFields(), expr.getFields(), coreTupleExpr);
  }

  private @Nullable Pair<@NotNull Expression, Concrete.@NotNull Expression>
  visitExprs(@NotNull List<? extends Expression> coreExpr,
             @NotNull List<? extends Concrete.Expression> expr,
             @NotNull Expression coreTupleExpr) {
    for (int i = 0; i < expr.size(); i++) {
      var accepted = expr.get(i).accept(this, coreExpr.get(i));
      if (accepted != null) return accepted;
    }
    return nullWithError(new SubExprError(SubExprError.Kind.ExprListNoMatch, coreTupleExpr));
  }

  @Override
  public Pair<Expression, Concrete.Expression> visitLet(Concrete.LetExpression expr, Expression coreExpr) {
    if (matchesSubExpr(expr)) return new Pair<>(coreExpr, expr);
    var coreLetExpr = coreExpr.cast(LetExpression.class);
    if (coreLetExpr == null) return nullWithError(SubExprError.mismatch(coreExpr));
    List<Concrete.LetClause> exprClauses = expr.getClauses();
    List<HaveClause> coreClauses = coreLetExpr.getClauses();
    for (int i = 0; i < exprClauses.size(); i++) {
      var accepted = visitLetClause(coreClauses.get(i), exprClauses.get(i));
      if (accepted != null) return accepted;
    }
    return expr.getExpression().accept(this, coreLetExpr.getExpression());
  }

  private @Nullable Pair<@NotNull Expression, Concrete.@NotNull Expression>
  visitLetClause(@NotNull HaveClause coreLetClause, @NotNull Concrete.LetClause exprLetClause) {
    var accepted = exprLetClause.getTerm().accept(this, coreLetClause.getExpression());
    if (accepted != null) return accepted;

    Concrete.Expression resultType = exprLetClause.getResultType();
    if (resultType == null)
      return nullWithError(new SubExprError(SubExprError.Kind.ConcreteHasNoTypeBinding, coreLetClause.getTypeExpr()));

    Expression coreResultType = coreLetClause.getTypeExpr();
    if (coreResultType instanceof PiExpression) {
      return visitPiImpl(exprLetClause.getParameters(), resultType, (PiExpression) coreResultType);
    } else return resultType.accept(this, coreResultType);
  }

  @Override
  public Pair<Expression, Concrete.Expression> visitTyped(Concrete.TypedExpression expr, Expression coreExpr) {
    if (matchesSubExpr(expr)) return new Pair<>(coreExpr, expr);
    return expr.expression.accept(this, coreExpr);
  }

  private @Nullable Pair<@NotNull Expression, Concrete.@NotNull Expression>
  visitClonedApp(@NotNull Concrete.AppExpression expr, @NotNull Expression coreExpr) {
    // This is a mutable reference
    List<Concrete.Argument> arguments = expr.getArguments();
    if (arguments.isEmpty()) return expr.getFunction().accept(this, coreExpr);

    int lastArgIndex = arguments.size() - 1;
    if (coreExpr instanceof AppExpression) {
      Concrete.Argument lastArgument = arguments.get(lastArgIndex);
      Expression function = coreExpr;
      AppExpression coreAppExpr;
      do {
        if (!(function instanceof AppExpression)) return null;
        coreAppExpr = (AppExpression) function;
        function = coreAppExpr.getFunction();
      } while (coreAppExpr.isExplicit() != lastArgument.isExplicit());
      var accepted = lastArgument.getExpression().accept(this, coreAppExpr.getArgument());
      if (accepted != null) return accepted;
      arguments.remove(lastArgIndex);
      return visitClonedApp(expr, function);
    } else if (coreExpr instanceof LamExpression) {
      // `f a` (concrete) gets elaborated to `\b -> f a b` (core) if `f` takes 2
      // arguments, so we try to match `f a` (concrete) and `f a b` (core),
      // ignoring the extra argument `b`.
      return visitClonedApp(expr, ((LamExpression) coreExpr).getBody());
    } else if (coreExpr instanceof DefCallExpression) {
      return visitDefCallArguments((DefCallExpression) coreExpr, arguments);
    } else return nullWithError(SubExprError.mismatch(coreExpr));
  }

  private @Nullable Pair<@NotNull Expression, Concrete.@NotNull Expression>
  visitDefCallArguments(@NotNull DefCallExpression expression,
                        @NotNull List<Concrete.Argument> arguments) {
    if (expression instanceof ClassCallExpression)
      return visitClassCallArguments((ClassCallExpression) expression, arguments.iterator());
    else return visitNonClassCallDefCallArguments(expression, arguments);
  }

  private @Nullable Pair<@NotNull Expression, Concrete.@NotNull Expression>
  visitClassCallArguments(@NotNull ClassCallExpression coreClassCall,
                          @NotNull Iterator<Concrete.Argument> arguments) {
    Map<ClassField, Expression> implementedHere = coreClassCall.getImplementedHere();
    Concrete.Argument argument = arguments.next();
    ClassDefinition definition = coreClassCall.getDefinition();
    for (ClassField field : definition.getFields()) {
      if (definition.isImplemented(field)) continue;
      if (argument.isExplicit() == field.getReferable().isExplicitField()) {
        Expression implementation = implementedHere.get(field);
        if (implementation == null) continue;
        var accepted = argument.getExpression().accept(this, implementation);
        if (accepted != null) return accepted;
        if (arguments.hasNext()) argument = arguments.next();
      }
    }
    return nullWithError(new SubExprError(SubExprError.Kind.Arguments, coreClassCall));
  }

  /**
   * Please always call {@link CorrespondedSubExprVisitor#visitDefCallArguments(DefCallExpression, List)}
   * instead.
   */
  private @Nullable Pair<@NotNull Expression, Concrete.@NotNull Expression>
  visitNonClassCallDefCallArguments(@NotNull DefCallExpression expression,
                                    @NotNull List<Concrete.Argument> argumentList) {
    Iterator<? extends Expression> defCallArgs = expression.getDefCallArguments().iterator();
    var arguments = argumentList.iterator();
    Concrete.Argument argument = arguments.next();
    DependentLink parameter = expression.getDefinition().getParameters();
    // In error messages, `Path A a a'` might become `a = a'`,
    // we treat this special case here.
    if (expression.getDefinition() == Prelude.PATH && argumentList.size() == 2) {
      parameter = parameter.getNext();
      defCallArgs.next();
    }
    for (; parameter.hasNext(); parameter = parameter.getNext()) {
      assert defCallArgs.hasNext();
      Expression coreArg = defCallArgs.next();
      // Take care of implicit application
      if (parameter.isExplicit() == argument.isExplicit()) {
        var accepted = argument.getExpression().accept(this, coreArg);
        if (accepted != null) return accepted;
        if (arguments.hasNext()) argument = arguments.next();
      }
    }
    return nullWithError(new SubExprError(SubExprError.Kind.Arguments, expression));
  }

  @Override
  public Pair<Expression, Concrete.Expression> visitApp(Concrete.AppExpression expr, Expression coreExpr) {
    if (matchesSubExpr(expr) || matchesSubExpr(expr.getFunction())) return new Pair<>(coreExpr, expr);
    Concrete.Expression function = expr.getFunction();
    Referable ref = function.getUnderlyingReferable();
    if (ref instanceof MetaReferable) {
      MetaDefinition meta = ((MetaReferable) ref).getDefinition();
      if (meta != null) {
        ConcreteExpression concrete = meta.checkAndGetConcreteRepresentation(expr.getArguments());
        if (concrete instanceof Concrete.Expression) {
          return ((Concrete.Expression) concrete).accept(this, coreExpr);
        }
      }
      return nullWithError(new SubExprError(SubExprError.Kind.MetaRef, coreExpr));
    }
    if (subExpr instanceof Concrete.AppExpression && Objects.equals(
        ((Concrete.AppExpression) subExpr).getFunction().getData(),
        function.getData()
    )) return new Pair<>(coreExpr, expr);
    if (subExpr instanceof Concrete.ReferenceExpression && matchesSubExpr(function))
      return new Pair<>(coreExpr, expr);
    Concrete.Expression cloned = Concrete.AppExpression.make(expr.getData(), function, new ArrayList<>(expr.getArguments()));
    return visitClonedApp(((Concrete.AppExpression) cloned), coreExpr);
  }

  @Override
  public Pair<Expression, Concrete.Expression> visitLam(Concrete.LamExpression expr, Expression coreExpr) {
    if (matchesSubExpr(expr)) return new Pair<>(coreExpr, expr);
    Expression body = coreExpr;
    for (Concrete.Parameter parameter : expr.getParameters()) {
      if (body instanceof LamExpression) {
        var coreLamExpr = (LamExpression) body;
        Concrete.Expression type = parameter.getType();
        if (type != null) {
          var ty = type.accept(this, coreLamExpr.getParameters().getTypeExpr());
          if (ty != null) return ty;
        }
        body = coreLamExpr.getBody();
      } else {
        return nullWithError(new SubExprError(SubExprError.Kind.ExpectLam, body));
      }
    }
    return expr.getBody().accept(this, body);
  }

  protected @Nullable Pair<Expression, Concrete.Expression> visitParameter(
      @NotNull Concrete.Parameter parameter,
      @NotNull DependentLink link
  ) {
    Concrete.Expression type = parameter.getType();
    Expression typeExpr = link.getTypeExpr();
    if (type == null)
      return nullWithError(new SubExprError(SubExprError.Kind.ConcreteHasNoTypeBinding, typeExpr));
    return type.accept(this, typeExpr);
  }

  @Nullable Pair<@NotNull Expression, Concrete.@NotNull Expression>
  visitPiImpl(List<? extends Concrete.Parameter> parameters,
              @NotNull Concrete.Expression codomain,
              @NotNull PiExpression corePi) {
    for (Concrete.Parameter parameter : parameters) {
      DependentLink link = corePi.getParameters();
      var expression = visitParameter(parameter, link);
      if (expression != null) return expression;
      Expression corePiCodomain = corePi.getCodomain();
      if (corePiCodomain instanceof PiExpression)
        corePi = (PiExpression) corePiCodomain;
      else return codomain.accept(this, corePiCodomain);
    }
    return codomain.accept(this, corePi);
  }

  @Nullable Pair<@NotNull Expression, Concrete.@NotNull Expression>
  visitSigmaParameters(List<? extends Concrete.Parameter> parameters, DependentLink sig) {
    for (Concrete.Parameter parameter : parameters) {
      if (!sig.hasNext()) {
        return null;
      }
      var expression = visitParameter(parameter, sig);
      if (expression != null) return expression;
      sig = sig.getNextTyped(null).getNext();
    }
    return nullWithError(new SubExprError(SubExprError.Kind.Telescope));
  }

  @Override
  public Pair<Expression, Concrete.Expression> visitPi(Concrete.PiExpression expr, Expression coreExpr) {
    if (matchesSubExpr(expr)) return new Pair<>(coreExpr, expr);
    var corePiExpr = coreExpr.cast(PiExpression.class);
    if (corePiExpr == null) return nullWithError(SubExprError.mismatch(coreExpr));
    return visitPiImpl(expr.getParameters(), expr.getCodomain(), corePiExpr);
  }

  @Override
  public Pair<Expression, Concrete.Expression> visitSigma(Concrete.SigmaExpression expr, Expression coreExpr) {
    if (matchesSubExpr(expr)) return new Pair<>(coreExpr, expr);
    var coreSigmaExpr = coreExpr.cast(SigmaExpression.class);
    if (coreSigmaExpr == null)
      return nullWithError(SubExprError.mismatch(coreExpr));
    return visitSigmaParameters(expr.getParameters(), coreSigmaExpr.getParameters());
  }

  static <T> @Nullable T visitElimBody(
    @NotNull List<? extends Concrete.Clause> clauses,
    @NotNull List<? extends ElimClause<Pattern>> coreClauses,
    BiFunction<ElimClause<Pattern>, Concrete.Clause, @Nullable T> function
  ) {
    // Interval pattern matching are stored in a special way,
    // maybe it's a TODO to implement it.
    if (clauses.size() != coreClauses.size()) return null;
    for (int i = 0; i < clauses.size(); i++) {
      T apply = function.apply(coreClauses.get(i), clauses.get(i));
      if (apply != null) return apply;
    }
    return null;
  }

  @Nullable Pair<@NotNull Expression, Concrete.@NotNull Expression> visitElimTree(
      List<Concrete.FunctionClause> clauses,
      List<? extends ElimClause<Pattern>> coreClauses
  ) {
    return visitElimBody(clauses, coreClauses, (coreClause, clause) -> {
      Concrete.Expression expression = clause.getExpression();
      if (expression == null)
        return nullWithError(new SubExprError(SubExprError.Kind.MissingExpr));
      return expression.accept(this, coreClause.getExpression());
    });
  }

  @Override
  public Pair<Expression, Concrete.Expression> visitCase(Concrete.CaseExpression expr, Expression coreExpr) {
    if (matchesSubExpr(expr)) return new Pair<>(coreExpr, expr);
    var coreCaseExpr = coreExpr.cast(CaseExpression.class);
    if (coreCaseExpr == null) return null;
    var expression = visitExprs(coreCaseExpr.getArguments(), expr
        .getArguments()
        .stream()
        .map(i -> i.expression)
        .collect(Collectors.toList()), coreCaseExpr);
    if (expression != null) return expression;
    Concrete.Expression resultType = expr.getResultType();
    if (resultType != null) {
      var accepted = resultType.accept(this, coreCaseExpr.getResultType());
      if (accepted != null) return accepted;
    }
    return visitElimTree(expr.getClauses(), coreCaseExpr.getElimBody().getClauses());
  }

  @Override
  public Pair<Expression, Concrete.Expression> visitEval(Concrete.EvalExpression expr, Expression coreExpr) {
    if (matchesSubExpr(expr)) return new Pair<>(coreExpr, expr);
    return expr.getExpression().accept(this, coreExpr);
  }

  @Override
  public Pair<Expression, Concrete.Expression> visitClassExt(Concrete.ClassExtExpression expr, Expression coreExpr) {
    if (matchesSubExpr(expr)) return new Pair<>(coreExpr, expr);
    var coreClassExpr = coreExpr.cast(ClassCallExpression.class);
    if (coreClassExpr == null) return nullWithError(SubExprError.mismatch(coreExpr));
    Map<ClassField, Expression> implementedHere = coreClassExpr.getImplementedHere();
    var field = visitStatements(implementedHere, expr.getStatements());
    if (field != null) return field;
    return expr.getBaseClassExpression().accept(this, coreClassExpr.getThisBinding().getTypeExpr());
  }

  private  @Nullable Pair<@NotNull Expression, Concrete.@NotNull Expression>
  visitStatements(Map<ClassField, Expression> implementedHere, List<Concrete.ClassFieldImpl> statements) {
    for (Concrete.ClassFieldImpl statement : statements) {
      var field = visitStatement(implementedHere, statement);
      if (field != null) return field;
    }
    return null;
  }

  @Nullable Pair<@NotNull Expression, Concrete.@NotNull Expression>
  visitStatement(@NotNull Map<ClassField, Expression> implementedHere, @NotNull Concrete.ClassFieldImpl statement) {
    Referable implementedField = statement.getImplementedField();
    if (implementedField == null) return nullWithError(new SubExprError(SubExprError.Kind.MissingImplementationField));
    // Class extension -- base class call.
    if (implementedField instanceof GlobalReferable && ((GlobalReferable) implementedField).getKind() != GlobalReferable.Kind.FIELD && statement.implementation != null) {
      var baseClassCall = implementedHere.entrySet()
          .stream()
          .filter(entry -> entry.getKey().getReferable() == implementedField)
          .map(Map.Entry::getValue)
          .filter(expr -> expr instanceof FieldCallExpression)
          .findFirst()
          .map(expr -> ((FieldCallExpression) expr))
          .map(e -> statement.implementation.accept(this, e.getArgument()));
      if (baseClassCall.isPresent()) return baseClassCall.get();
    }
    Optional<Expression> fieldExpr = implementedHere.entrySet()
        .stream()
        .filter(entry -> entry.getKey().getReferable() == implementedField)
        .findFirst()
        .map(Map.Entry::getValue);
    if (fieldExpr.isEmpty())
      return nullWithError(new SubExprError(SubExprError.Kind.FieldNotFound));
    Expression field = fieldExpr.get();
    if (statement.implementation != null)
      return statement.implementation.accept(this, field);
    else if (field instanceof NewExpression)
      return visitStatements(
          ((NewExpression) field).getClassCall().getImplementedHere(),
          statement.getSubCoclauseList()
      );
    else return nullWithError(new SubExprError(SubExprError.Kind.FieldNotFound));
  }

  @Override
  public Pair<Expression, Concrete.Expression> visitBinOpSequence(Concrete.BinOpSequenceExpression expr, Expression coreExpr) {
    if (matchesSubExpr(expr)) return new Pair<>(coreExpr, expr);
    throw new IllegalStateException("BinOpSequence shouldn't appear");
  }
}
