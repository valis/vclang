package org.arend.typechecking.termination;

import org.arend.core.context.param.DependentLink;
import org.arend.core.context.param.EmptyDependentLink;
import org.arend.core.definition.Definition;
import org.arend.core.expr.DefCallExpression;
import org.arend.core.expr.Expression;
import org.arend.core.expr.SigmaExpression;
import org.arend.ext.prettyprinting.PrettyPrinterConfig;
import org.arend.ext.prettyprinting.doc.Doc;
import org.arend.util.Pair;
import org.jetbrains.annotations.Nullable;

import java.util.HashMap;

import static org.arend.ext.prettyprinting.doc.DocFactory.*;

class CallMatrix extends LabeledCallMatrix {
  private final DefCallExpression myCallExpression;
  private final Definition myEnclosingDefinition;
  private final HashMap<DependentLink, Pair<Integer, Integer>> myCallExpressionIndexRanges = new HashMap<>();
  private final HashMap<DependentLink, Pair<Integer, Integer>> myDefinitionIndexRanges = new HashMap<>();

  CallMatrix(Definition enclosingDefinition, DefCallExpression call) {
    super(calculateDimension(call.getDefinition().getParameters()), calculateDimension(enclosingDefinition.getParameters()));
    myCallExpression = call;
    myEnclosingDefinition = enclosingDefinition;
    initIndexRanges(call.getDefinition().getParameters(), myCallExpressionIndexRanges, 0);
    initIndexRanges(enclosingDefinition.getParameters(), myDefinitionIndexRanges, 0);
  }

  @Override
  public Definition getCodomain() {
    return myCallExpression.getDefinition();
  }

  @Override
  public Definition getDomain() {
    return myEnclosingDefinition;
  }

  @Override
  public int getCompositeLength() {
    return 1;
  }

  @Override
  public Doc getMatrixLabel(PrettyPrinterConfig ppConfig) { //Caution: printing matrix label of a call of a nonterminating function may lead to stack overflow
    return hang(hList(refDoc(myEnclosingDefinition.getReferable()), text(" ->")), termDoc(myCallExpression, ppConfig));
  }

  public void setBlock(DependentLink i, DependentLink j, R value) {
    Pair<Integer, Integer> rangeI = myDefinitionIndexRanges.get(i);
    Pair<Integer, Integer> rangeJ = myCallExpressionIndexRanges.get(j);
    int lenI = rangeI.proj2 - rangeI.proj1 + 1;
    int lenJ = rangeJ.proj2 - rangeJ.proj1 + 1;
    if (lenI == 1 && lenJ == 1) {
      this.set(rangeI.proj1, rangeJ.proj1, value);
    } else if (lenI == lenJ) switch (value) {
      case Equal:
        for (int ii = rangeI.proj1; ii <= rangeI.proj2; ii++)
          this.set(ii, rangeJ.proj1 + ii - rangeI.proj1, R.Equal);
      case Unknown:
        for (int ii = rangeI.proj1; ii <= rangeI.proj2; ii++)
          for (int jj = rangeJ.proj1; jj <= rangeJ.proj2; jj++)
            if (ii - rangeI.proj1 != jj - rangeJ.proj1)
              this.set(ii, jj, R.Unknown);
        break;
      case LessThan:
        throw new IllegalStateException();
    }
    else throw new IllegalStateException();
  }

  @Override
  protected String[] getColumnLabels() {
    String[] result = new String[getWidth()];
    DependentLink arg = getCodomain().getParameters();
    for (int j = 0; j < getWidth(); j++)
      result[j] = calculateLabel(arg, j, 1, "");
    return result;
  }


  @Override
  protected String[] getRowLabels() {
    String[] result = new String[getHeight()];
    DependentLink arg = getDomain().getParameters();
    for (int j = 0; j < getHeight(); j++)
      result[j] = calculateLabel(arg, j, 1, "");
    return result;
  }

  private static String calculateLabel(DependentLink parameter, int queriedIndex, int parameterIndex, String namePrefix) {
    if (!(parameter instanceof EmptyDependentLink)) {
      DependentLink unfoldedParameters = unfoldSigmaType(parameter);
      String parameterName = parameter.getName();
      if (parameterName == null) parameterName = String.valueOf(parameterIndex);
      String dotPrefix = namePrefix;
      if (!dotPrefix.isEmpty()) dotPrefix = dotPrefix + ".";

      int length = 1;
      if (unfoldedParameters != null) {
        String result = calculateLabel(unfoldedParameters, queriedIndex, 1,dotPrefix + parameterName);
        if (result != null) return result;
        length = calculateDimension(unfoldedParameters);
      } else {
        if (queriedIndex == 0) return dotPrefix + parameterName;
      }

      return calculateLabel(parameter.getNext(), queriedIndex - length, parameterIndex + 1, namePrefix);
    }
    return null;
  }

  private static int initIndexRanges(DependentLink parameter, @Nullable HashMap<DependentLink, Pair<Integer, Integer>> indexRanges, int currIndex) {
    int length = 1;
    if (!(parameter instanceof EmptyDependentLink)) {
      DependentLink unfoldedParameters = unfoldSigmaType(parameter);
      if (unfoldedParameters != null) {
        length = initIndexRanges(unfoldedParameters, indexRanges, currIndex);
      }
      if (indexRanges != null) indexRanges.put(parameter, new Pair<>(currIndex, currIndex + length - 1));
      return length + initIndexRanges(parameter.getNext(), indexRanges, currIndex + length);
    }
    return 0;
  }

  private static int calculateDimension(DependentLink link) {
    return initIndexRanges(link, null, 0);
  }

  @Nullable
  public static DependentLink unfoldSigmaType(DependentLink parameter) {
    Expression type = parameter.getType().getExpr();
    if (type instanceof SigmaExpression) {
      return ((SigmaExpression) type).getParameters();
    }
    return null;
  }
}
