package org.arend.ext.core.expr;

import org.arend.ext.core.body.CoreBody;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.context.CoreParameter;
import org.arend.ext.core.definition.CoreDefinition;
import org.arend.ext.core.definition.CoreFunctionDefinition;
import org.arend.ext.core.ops.CMP;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.prettyprinting.PrettyPrintable;
import org.arend.ext.typechecking.TypedExpression;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.List;
import java.util.Set;
import java.util.function.Function;

/**
 * A core expression is an internal representation of Arend expressions.
 */
public interface CoreExpression extends CoreBody, UncheckedExpression, AbstractedExpression, PrettyPrintable {
  <P, R> R accept(@NotNull CoreExpressionVisitor<? super P, ? extends R> visitor, P params);

  /**
   * Expressions produces during type-checking may not implement the correct interface.
   * This method returns the underlying expression which always implements it.
   * Note that expressions stored in type-checked definitions are always correct, so this method just returns the expression itself for them.
   */
  @Override @NotNull CoreExpression getUnderlyingExpression();

  /**
   * Computes the type of this expression.
   */
  @NotNull CoreExpression computeType();

  /**
   * Computes the type of this expression and returns the expression with the type.
   */
  @NotNull TypedExpression computeTyped();

  /**
   * Normalizes expression.
   */
  @Override @NotNull CoreExpression normalize(@NotNull NormalizationMode mode);

  /**
   * Unfolds all occurrences of given functions and fields in this expression.
   *
   * @param definitions a set of functions and fields to unfold.
   * @param unfolded    definitions that are actually unfolded will be added to this set.
   * @param unfoldLet   unfolds \\let expressions if {@code true}.
   */
  @Override @NotNull CoreExpression unfold(@NotNull Set<? extends CoreDefinition> definitions, @Nullable Set<CoreDefinition> unfolded, boolean unfoldLet);

  /**
   * Removes pi parameters and returns the codomain.
   *
   * @param parameters  parameters of the pi-expression will be added to this list; if it is {@code null}, they will be discarded.
   * @return            the codomain of the pi-expression, or the expression itself if it is not a pi-expression.
   */
  @NotNull CoreExpression getPiParameters(@Nullable List<? super CoreParameter> parameters);

  /**
   * If {@code this} is \lam (x_1 : A_1) ... (x_n : A_n) => B, returns \Pi (x_1 : A_1) ... (x_n : A_n) -> B.
   * If B is not a type, returns {@code null}.
   */
  @Nullable CoreExpression lambdaToPi();

  enum FindAction { CONTINUE, STOP, SKIP }

  /**
   * Applies the given function to every subexpression of this expression.
   * If the function returns
   * <ul>
   * <li>{@link FindAction#CONTINUE}, then the method proceeds processing other subexpressions.</li>
   * <li>{@link FindAction#STOP}, then the method halts.</li>
   * <li>{@link FindAction#SKIP}, then the method skips subexpressions of the current expressions.</li>
   * </ul>
   *
   * @return true if {@code function} returns {@link FindAction#STOP} on some subexpression.
   */
  boolean processSubexpression(@NotNull Function<CoreExpression, FindAction> function);

  /**
   * Compares this expression with another one.
   *
   * @param expr2   another expression
   * @param cmp     indicates whether expressions should be compared on equality or inequality
   * @return        true if expressions are equal; false otherwise
   */
  boolean compare(@NotNull UncheckedExpression expr2, @NotNull CMP cmp);

  /**
   * Returns an expression equivalent to this one in which the given binding does not occur.
   * Returns {@code null} if the binding cannot be eliminated from this expression.
   */
  @Override @Nullable CoreExpression removeUnusedBinding(@NotNull CoreBinding binding);

  /**
   * Checks that this expression is equivalent to a lambda expression such that its parameters does not occur in its body.
   * Returns the body of the lambda or {@code null} if this expression is not a lambda or if its parameter occurs in the body.
   */
  @Override @Nullable CoreExpression removeConstLam();

  /**
   * Checks that this expression is equivalent to expression of the form {@code a = a'}.
   * @return  an expression of the form {@code a = a'} equivalent to this one or {@code null} if there is no such expression.
   */
  @Nullable CoreFunCallExpression toEquality();
}
