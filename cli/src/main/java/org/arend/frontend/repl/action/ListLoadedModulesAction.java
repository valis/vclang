package org.arend.frontend.repl.action;

import org.arend.frontend.repl.CommonCliRepl;
import org.jetbrains.annotations.Nls;
import org.jetbrains.annotations.NotNull;

import java.util.function.Supplier;
import java.util.stream.Collectors;

public final class ListLoadedModulesAction implements CliReplCommand {
  public static final @NotNull ListLoadedModulesAction INSTANCE = new ListLoadedModulesAction();

  private ListLoadedModulesAction() {
  }

  @Override
  public void invoke(@NotNull String line, @NotNull CommonCliRepl api, @NotNull Supplier<@NotNull String> scanner) {
    var string = api.getReplLibrary().getLoadedModules().stream().map(String::valueOf).collect(Collectors.joining(" "));
    if (string.isBlank()) api.println("[INFO] No modules loaded.");
    else api.println(string);
  }

  @Override
  public @Nls(capitalization = Nls.Capitalization.Sentence) @NotNull String description() {
    return "List all loaded modules";
  }
}
