package com.jetbrains.jetpad.vclang.module.source;

import com.jetbrains.jetpad.vclang.error.ErrorReporter;
import com.jetbrains.jetpad.vclang.module.ModulePath;
import com.jetbrains.jetpad.vclang.term.Concrete;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;

public interface SourceSupplier<SourceIdT extends SourceId> {
  SourceIdT locateModule(@Nonnull ModulePath modulePath);
  boolean isAvailable(@Nonnull SourceIdT sourceId);
  LoadResult loadSource(@Nonnull SourceIdT sourceId, @Nonnull ErrorReporter errorReporter);
  long getAvailableVersion(@Nonnull SourceIdT sourceId);

  class LoadResult {
    public final @Nonnull Concrete.ClassDefinition definition;
    public final long version;

    public LoadResult(@Nonnull Concrete.ClassDefinition definition, long version) {
      this.definition = definition;
      this.version = version;
    }

    public static LoadResult make(@Nullable Concrete.ClassDefinition result, long version) {
      return result != null ? new LoadResult(result, version) : null;
    }
  }
}
