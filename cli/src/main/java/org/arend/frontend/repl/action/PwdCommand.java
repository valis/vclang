package org.arend.frontend.repl.action;

import org.arend.frontend.repl.CommonCliRepl;
import org.jetbrains.annotations.Nls;
import org.jetbrains.annotations.NotNull;

import java.util.function.Supplier;

public final class PwdCommand implements CliReplCommand {
  @Override
  public @Nls(capitalization = Nls.Capitalization.Sentence) @NotNull String description() {
    return "Show current working directory";
  }

  @Override
  public void invoke(@NotNull String line, @NotNull CommonCliRepl api, @NotNull Supplier<@NotNull String> scanner) {
    api.println(api.pwd);
  }
}
