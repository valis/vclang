package org.arend.typechecking.patternmatching;

import org.arend.Matchers;
import org.arend.typechecking.TypeCheckingTestCase;
import org.arend.typechecking.error.local.CertainTypecheckingError;
import org.arend.typechecking.error.local.NotEqualExpressionsError;
import org.junit.Test;

public class LamPatternTest extends TypeCheckingTestCase {
  @Test
  public void tupleTest() {
    typeCheckDef("\\func test : Nat -> (\\Sigma Nat Nat) -> Nat -> Nat => \\lam a (x,_) b => x");
  }

  @Test
  public void tupleTest2() {
    typeCheckDef("\\func test : (\\Sigma Nat Nat) -> (\\Sigma Nat (\\Sigma Nat Nat)) -> Nat => \\lam (a,_) (_,(b,_)) => a Nat.+ b");
  }

  @Test
  public void finTest() {
    typeCheckDef("\\func test : Fin 1 -> Nat => \\lam 0 => 3");
  }

  @Test
  public void recordTest() {
    typeCheckModule(
      "\\record R (x y : Nat)\n" +
      "\\func test : R -> Nat => \\lam (x,y) => y");
  }

  @Test
  public void dataTest() {
    typeCheckModule(
      "\\data D | con Nat\n" +
      "\\func test : D -> Nat => \\lam (con x) => x");
  }

  @Test
  public void implicitTest() {
    typeCheckDef("\\func test : \\Pi {x : Fin 1} -> x = 0 => \\lam {(zero)} => idp");
  }

  @Test
  public void implicitError() {
    typeCheckDef("\\func test : \\Pi {x : Fin 1} -> x = 0 => \\lam {zero} => idp", 1);
    assertThatErrorsAre(Matchers.typecheckingError(NotEqualExpressionsError.class));
  }

  @Test
  public void projTest() {
    typeCheckModule(
      "\\func proj : (\\Sigma Nat Nat) -> Nat => \\lam (x,_) => x\n" +
      "\\func test : proj = (\\lam p => p.1) => idp");
  }

  @Test
  public void dependencyTest() {
    typeCheckDef("\\func test : \\Pi (x : Fin 1) -> x = 0 -> 0 = 0 => \\lam 0 p => p");
  }

  @Test
  public void absurdPatternTest() {
    typeCheckModule(
      "\\data Bool | true | false\n" +
      "\\data D (x y : Bool) \\with\n" +
      "  | false, true => con\n" +
      "\\func test : \\Pi (x : Bool) -> D x x -> 0 = 1 => \\lam (true) ()");
  }

  @Test
  public void idpTest() {
    typeCheckDef("\\func test : \\Pi (x : Nat) -> x = 0 -> 0 = x => \\lam x (idp) => idp");
  }

  @Test
  public void coclauseTest() {
    typeCheckModule(
      "\\record R | f : (\\Sigma Nat Nat) -> Nat\n" +
      "\\func test : R \\cowith\n" +
      "  | f (x,y) => x");
  }

  @Test
  public void fieldImplTest() {
    typeCheckModule(
      "\\record R | f : (\\Sigma Nat Nat) -> Nat\n" +
      "\\record S \\extends R\n" +
      "  | f (x,y) => x");
  }

  @Test
  public void coclauseFunctionTest() {
    parseModule(
      "\\record R | f : (\\Sigma Nat Nat) -> Nat\n" +
      "\\func test : R \\cowith\n" +
      "  | f (x,y) : Nat => x", 1);
  }

  @Test
  public void letTest() {
    typeCheckModule(
      "\\data D | con Nat\n" +
      "\\func test (f : Nat -> D) : Nat => \\let (con n) => f 0 \\in n");
  }

  @Test
  public void letTest2() {
    typeCheckModule(
      "\\data D | con Nat\n" +
      "\\func test (f : Nat -> D) : Nat => \\let | (con n) => f 0 | (con m) => f 1 \\in n Nat.+ m");
  }

  @Test
  public void letTest3() {
    typeCheckModule(
      "\\data D | con Nat\n" +
      "\\func test (f : Nat -> D) : Nat => \\let | (con n) => f 0 | (con m) => f n \\in m");
  }

  @Test
  public void letError() {
    typeCheckModule(
      "\\data D | con Nat\n" +
      "\\func test (f : Nat -> D) : Nat => \\let | {con n} => f 0 \\in n", 1);
    assertThatErrorsAre(Matchers.typecheckingError(CertainTypecheckingError.Kind.EXPECTED_EXPLICIT_PATTERN));
  }

  @Test
  public void asLamTest() {
    typeCheckModule(
      "\\data D | con Nat\n" +
      "\\func f : D -> D => \\lam (con n \\as d) => d\n" +
      "\\func test (x : D) : f x = x\n" +
      "  | con n => idp");
  }

  @Test
  public void asLetTest() {
    typeCheckModule(
      "\\data D | con Nat\n" +
      "\\func f (x : D) : D => \\let (con n \\as d) => x \\in d\n" +
      "\\func test (x : D) : f x = x\n" +
      "  | con n => idp");
  }

  @Test
  public void caseAsLetTest() {
    typeCheckModule(
      "\\data D | con Nat\n" +
      "\\func test (x : D) : \\Sigma (n : Nat) (x = con n)\n" +
      "  => \\let | (con n \\as d) => x\n" +
      "           | p : x = d => idp\n" +
      "     \\in (n,p)");
  }

  @Test
  public void absurdPatternLetTest() {
    typeCheckModule(
      "\\data Bool | true | false\n" +
      "\\data D (x y : Bool) \\with\n" +
      "  | false, true => con\n" +
      "\\func test (x : Bool) (p : D x x) : 0 = 1\n" +
      "  => \\let | (true) => x | () => p");
  }
}
