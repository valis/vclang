package org.arend.core.expr;

import org.arend.core.context.param.DependentLink;
import org.arend.core.definition.ClassDefinition;
import org.arend.core.definition.ClassField;
import org.arend.core.expr.type.Type;
import org.arend.core.expr.visitor.ExpressionVisitor;
import org.arend.core.expr.visitor.NormalizeVisitor;
import org.arend.core.expr.visitor.StripVisitor;
import org.arend.core.sort.Sort;
import org.arend.core.subst.ExprSubstitution;
import org.arend.core.subst.LevelSubstitution;
import org.arend.core.subst.SubstVisitor;
import org.arend.typechecking.error.LocalErrorReporter;

import java.util.HashMap;
import java.util.Map;

public class ClassCallExpression extends DefCallExpression implements Type {
  private final Sort mySortArgument;
  private final Map<ClassField, Expression> myImplementations;
  private final Sort mySort;

  public ClassCallExpression(ClassDefinition definition, Sort sortArgument) {
    super(definition);
    mySortArgument = sortArgument;
    myImplementations = new HashMap<>();
    mySort = definition.getSort();
  }

  public ClassCallExpression(ClassDefinition definition, Sort sortArgument, Map<ClassField, Expression> implementations, Sort sort) {
    super(definition);
    mySortArgument = sortArgument;
    myImplementations = implementations;
    mySort = sort;
  }

  public Map<ClassField, Expression> getImplementedHere() {
    return myImplementations;
  }

  public Expression getImplementationHere(ClassField field) {
    return myImplementations.get(field);
  }

  public Expression getImplementation(ClassField field, Expression thisExpr) {
    Expression expr = myImplementations.get(field);
    if (expr != null) {
      return expr;
    }
    LamExpression impl = getDefinition().getImplementation(field);
    return impl == null ? null : impl.substArgument(thisExpr);
  }

  public boolean isImplemented(ClassField field) {
    return myImplementations.containsKey(field) || getDefinition().isImplemented(field);
  }

  public boolean isUnit() {
    return myImplementations.size() + getDefinition().getImplemented().size() == getDefinition().getFields().size();
  }

  public DependentLink getClassFieldParameters() {
    return getDefinition().getClassFieldParameters(getSortArgument());
  }

  @Override
  public ClassDefinition getDefinition() {
    return (ClassDefinition) super.getDefinition();
  }

  @Override
  public Sort getSortArgument() {
    return mySortArgument;
  }

  @Override
  public Expression getExpr() {
    return this;
  }

  @Override
  public Sort getSortOfType() {
    return getSort();
  }

  @Override
  public ClassCallExpression subst(ExprSubstitution exprSubstitution, LevelSubstitution levelSubstitution) {
    return new SubstVisitor(exprSubstitution, levelSubstitution).visitClassCall(this, null);
  }

  @Override
  public ClassCallExpression strip(LocalErrorReporter errorReporter) {
    return new StripVisitor(errorReporter).visitClassCall(this, null);
  }

  @Override
  public ClassCallExpression normalize(NormalizeVisitor.Mode mode) {
    return NormalizeVisitor.INSTANCE.visitClassCall(this, mode);
  }

  public Sort getSort() {
    return mySort;
  }

  @Override
  public <P, R> R accept(ExpressionVisitor<? super P, ? extends R> visitor, P params) {
    return visitor.visitClassCall(this, params);
  }
}