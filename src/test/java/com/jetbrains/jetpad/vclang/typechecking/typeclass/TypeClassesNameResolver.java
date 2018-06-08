package com.jetbrains.jetpad.vclang.typechecking.typeclass;

import com.jetbrains.jetpad.vclang.naming.NameResolverTestCase;
import org.junit.Test;

public class TypeClassesNameResolver extends NameResolverTestCase {
  @Test
  public void classNotInScope() {
    resolveNamesModule("\\class Y => X", 1);
  }

  @Test
  public void fieldSynonymNotInScope() {
    resolveNamesModule(
      "\\class X (A : \\Type0)\n" +
      "\\class Y => X { B => C }", 1);
  }

  @Test
  public void resolveFieldSynonym() {
    resolveNamesModule(
        "\\class X (T : \\Type0) {\n" +
        "  | f : \\Type0\n" +
        "}\n" +
        "\\class X' => X { f => f' }\n" +
        "\\func g {x : X} => f\n" +
        "\\func h (x : X) => x.f\n" +
        "\\func g' {x' : X'} => f'\n" +
        "\\func h' (x' : X') => x'.f'");
  }

  @Test
  public void resolveFieldSynonymError() {
    resolveNamesModule(
        "\\class X (T : \\Type0) {\n" +
        "  | f : \\Type0\n" +
        "}\n" +
        "\\class X' => X { f => f' }\n" +
        "\\func h (x' : X') => x'.f", 1);
  }

  @Test
  public void resolveNamesDuplicate() {
    resolveNamesModule(
        "\\class X (T : \\Type0) {\n" +
        "  | f : \\Type0\n" +
        "}\n" +
        "\\class X' => X { f => h }\n" +
        "\\class Y (T : \\Type0) {\n" +
        "  | g : \\Type0 -> \\Type0\n" +
        "}\n" +
        "\\class Y' => Y { g => h }", 1);
  }

  @Test
  public void resolveNamesInner() {
    resolveNamesModule(
        "\\class X \\where {\n" +
        "  \\class Z (T : \\Type0) {\n" +
        "    | f : \\Type0\n" +
        "  }\n" +
        "  \\class Z' => Z { f => f' }\n" +
        "}\n" +
        "\\func g => f'", 1);
  }

  @Test
  public void resolveClassExt() {
    resolveNamesModule(
        "\\class X (T : \\Type1) {\n" +
        "  | f : \\Type1\n" +
        "}\n" +
        "\\class Y => X { f => g }\n" +
        "\\func h => \\new Y { T => \\Type0 | g => \\Type0 }");
  }

  @Test
  public void resolveClassExtSameName() {
    resolveNamesModule(
        "\\class X (T : \\Type1) {\n" +
        "  | f : \\Type1\n" +
        "}\n" +
        "\\class Y => X\n" +
        "\\func h => \\new Y { T => \\Type0 | f => \\Type0 }");
  }

  @Test
  public void resolveClassExtError() {
    resolveNamesModule(
        "\\class X (T : \\Type1) {\n" +
        "  | f : \\Type1\n" +
        "}\n" +
        "\\class Y => X { f => g }\n" +
        "\\func h => \\new Y { T => \\Type0 | f => \\Type0 }", 1);
  }

  @Test
  public void duplicateFieldSynonymName() {
    resolveNamesModule(
        "\\class X (T f : \\Type0)\n" +
        "\\func g => 0\n" +
        "\\class Y => X { f => g }", 1);
  }

  @Test
  public void cyclicSynonym() {
    resolveNamesModule("\\class X => X", 1);
  }

  @Test
  public void instanceRecord() {
    resolveNamesModule(
      "\\record X (A : \\Type0) {\n" +
      "  | B : A -> \\Type0\n" +
      "}\n" +
      "\\data D\n" +
      "\\instance D-X : X | A => D | B => \\lam n => D", 1);
  }
}
