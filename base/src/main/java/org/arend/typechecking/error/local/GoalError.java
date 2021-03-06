package org.arend.typechecking.error.local;

import org.arend.core.context.binding.Binding;
import org.arend.core.context.binding.EvaluatingBinding;
import org.arend.core.expr.Expression;
import org.arend.core.subst.ExprSubstitution;
import org.arend.ext.error.GeneralError;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.prettyprinting.PrettyPrinterConfig;
import org.arend.ext.prettyprinting.doc.Doc;
import org.arend.ext.typechecking.GoalSolver;
import org.arend.naming.reference.GeneratedLocalReferable;
import org.arend.naming.reference.LocalReferable;
import org.arend.naming.reference.Referable;
import org.arend.term.concrete.Concrete;
import org.arend.typechecking.TypecheckingContext;
import org.arend.typechecking.patternmatching.Condition;

import java.util.*;

import static org.arend.ext.prettyprinting.doc.DocFactory.*;

public class GoalError extends TypecheckingError {
  public final TypecheckingContext typecheckingContext;
  public final Map<Binding, Expression> bindingTypes;
  public final Expression expectedType;
  public final Concrete.Expression result;
  public final List<GeneralError> errors;
  public final GoalSolver goalSolver;
  private final ExprSubstitution substitution;
  private List<Condition> myConditions = Collections.emptyList();

  public GoalError(TypecheckingContext typecheckingContext, Map<Binding, Expression> bindingTypes, Expression expectedType, Concrete.Expression result, List<GeneralError> errors, GoalSolver goalSolver, Concrete.GoalExpression expression) {
    super(Level.GOAL, "Goal" + (expression.getName() == null ? "" : " " + expression.getName()), expression);
    this.typecheckingContext = typecheckingContext;
    this.bindingTypes = bindingTypes;
    this.result = result;
    this.errors = errors;
    this.goalSolver = goalSolver;

    substitution = new ExprSubstitution();
    if (typecheckingContext != null) {
      for (Iterator<Map.Entry<Referable, Binding>> iterator = typecheckingContext.localContext.entrySet().iterator(); iterator.hasNext(); ) {
        Map.Entry<Referable, Binding> entry = iterator.next();
        if (entry.getKey() instanceof GeneratedLocalReferable && entry.getValue() instanceof EvaluatingBinding) {
          substitution.add(entry.getValue(), ((EvaluatingBinding) entry.getValue()).getExpression());
          iterator.remove();
        }
      }
    }

    this.expectedType = expectedType == null ? null : expectedType.subst(substitution);
  }

  @Override
  public Concrete.GoalExpression getCauseSourceNode() {
    return (Concrete.GoalExpression) super.getCauseSourceNode();
  }

  @Override
  public Doc getBodyDoc(PrettyPrinterConfig ppConfig) {
    Doc expectedDoc = expectedType == null ? nullDoc() : hang(text("Expected type:"), expectedType.prettyPrint(ppConfig));

    Doc contextDoc;
    Map<Referable, Binding> context = typecheckingContext == null ? Collections.emptyMap() : typecheckingContext.localContext;
    if (!context.isEmpty()) {
      List<Doc> contextDocs = new ArrayList<>(context.size());
      for (Map.Entry<Referable, Binding> entry : context.entrySet()) {
        if (!entry.getValue().isHidden() && (!(entry.getKey() instanceof LocalReferable) || !((LocalReferable) entry.getKey()).isHidden())) {
          Expression type = bindingTypes.get(entry.getValue());
          if (type == null) type = entry.getValue().getTypeExpr();
          if (type != null) type = type.subst(substitution);
          contextDocs.add(hang(hList(entry.getKey() == null ? text("_") : refDoc(entry.getKey()), text(" :")), type == null ? text("{?}") : termDoc(type, ppConfig)));
        }
      }
      contextDoc = contextDocs.isEmpty() ? nullDoc() : hang(text("Context:"), vList(contextDocs));
    } else {
      contextDoc = nullDoc();
    }

    Doc conditionsDoc;
    if (!myConditions.isEmpty()) {
      List<Doc> conditionsDocs = new ArrayList<>(myConditions.size());
      for (Condition condition : myConditions) {
        conditionsDocs.add(condition.toDoc(ppConfig));
      }
      conditionsDoc = hang(text("Conditions:"), vList(conditionsDocs));
    } else {
      conditionsDoc = nullDoc();
    }

    Doc errorsDoc;
    if (!errors.isEmpty()) {
      List<Doc> errorsDocs = new ArrayList<>(errors.size());
      for (GeneralError error : errors) {
        errorsDocs.add(hang(error.getHeaderDoc(ppConfig), error.getBodyDoc(ppConfig)));
      }
      errorsDoc = hang(text("Errors:"), vList(errorsDocs));
    } else {
      errorsDoc = nullDoc();
    }

    return vList(expectedDoc, contextDoc, conditionsDoc, errorsDoc);
  }

  @Override
  public boolean hasExpressions() {
    return true;
  }


  public void addCondition(Condition condition) {
    if (myConditions.isEmpty()) {
      myConditions = new ArrayList<>();
    }
    myConditions.add(condition);
  }

  public List<? extends Condition> getConditions() {
    return myConditions;
  }
}
