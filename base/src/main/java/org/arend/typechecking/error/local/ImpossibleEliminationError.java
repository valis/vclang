package org.arend.typechecking.error.local;

import org.arend.core.expr.DataCallExpression;
import org.arend.core.subst.ExprSubstitution;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.prettyprinting.PrettyPrinterConfig;
import org.arend.ext.prettyprinting.doc.Doc;
import org.arend.term.concrete.Concrete;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import static org.arend.ext.prettyprinting.doc.DocFactory.*;

public class ImpossibleEliminationError extends TypecheckingError {
  public final DataCallExpression dataCall;
  public final ExprSubstitution substitution;

  public ImpossibleEliminationError(DataCallExpression dataCall, @NotNull Concrete.SourceNode cause, @Nullable ExprSubstitution substitution) {
    super("Elimination is not possible here, cannot determine the set of eligible constructors", cause);
    this.dataCall = dataCall;
    this.substitution = substitution;
  }

  @Override
  public Doc getBodyDoc(PrettyPrinterConfig ppConfig) {
    return hList(text("for data "), termLine(dataCall, ppConfig));
  }

  @Override
  public boolean hasExpressions() {
    return true;
  }
}
