package org.arend.frontend.repl.action;

import org.arend.ext.module.ModulePath;
import org.arend.frontend.repl.CommonCliRepl;
import org.arend.naming.scope.Scope;
import org.jetbrains.annotations.Nls;
import org.jetbrains.annotations.NotNull;

import java.util.function.Supplier;

public final class UnloadModuleCommand implements CliReplCommand {
  public static final @NotNull UnloadModuleCommand INSTANCE = new UnloadModuleCommand();

  private UnloadModuleCommand() {
  }

  @Override
  public @Nls(capitalization = Nls.Capitalization.Sentence) @NotNull String description() {
    return "Unload an Arend module loaded before";
  }

  @Override
  public void invoke(@NotNull String line, @NotNull CommonCliRepl api, @NotNull Supplier<@NotNull String> scanner) {
    var modulePath = ModulePath.fromString(line);
    if (!api.getReplLibrary().containsModule(modulePath)) {
      api.eprintln("[ERROR] Module " + modulePath + " is not loaded.");
      return;
    }
    Scope scope = api.getAvailableModuleScopeProvider().forModule(modulePath);
    if (scope != null) api.removeScope(scope);
    boolean isUnloaded = api.unloadModule(modulePath);
    assert isUnloaded;
    api.checkErrors();
  }
}
