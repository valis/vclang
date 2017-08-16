package com.jetbrains.jetpad.vclang.typechecking.error;

import com.jetbrains.jetpad.vclang.error.GeneralError;
import com.jetbrains.jetpad.vclang.error.doc.Doc;
import com.jetbrains.jetpad.vclang.term.Abstract;
import com.jetbrains.jetpad.vclang.term.provider.SourceInfoProvider;
import com.jetbrains.jetpad.vclang.typechecking.error.local.LocalTypeCheckingError;

import javax.annotation.Nonnull;

import static com.jetbrains.jetpad.vclang.error.doc.DocFactory.*;

/**
 * If you would like to add a new type checking error, please, extend {@link LocalTypeCheckingError} instead.
 */
public class TypeCheckingError extends GeneralError {
  public final Abstract.Definition definition;
  public final LocalTypeCheckingError localError;

  public TypeCheckingError(@Nonnull Abstract.Definition definition, LocalTypeCheckingError localError) {
    super(localError.level, localError.message, localError.cause);
    this.definition = definition;
    this.localError = localError;
  }

  @Override
  public Doc getDoc(SourceInfoProvider src) {
    return vHang(localError.getDoc(src), hList(text("While typechecking: "), refDoc(definition)));
  }
}
