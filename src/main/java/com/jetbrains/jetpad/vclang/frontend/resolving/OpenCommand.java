package com.jetbrains.jetpad.vclang.frontend.resolving;

import com.jetbrains.jetpad.vclang.module.ModulePath;
import com.jetbrains.jetpad.vclang.naming.reference.GlobalReferable;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.util.List;

public interface OpenCommand {
  @Nullable ModulePath getModulePath();
  @Nonnull List<String> getPath();
  @Nullable
  GlobalReferable getResolvedClass();

  boolean isHiding();
  @Nullable List<String> getNames();
}
