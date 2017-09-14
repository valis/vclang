package com.jetbrains.jetpad.vclang.naming.scope;

import com.jetbrains.jetpad.vclang.naming.reference.Referable;
import com.jetbrains.jetpad.vclang.term.Concrete;

import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Set;

public class SingletonScope implements Scope {
  private final Referable myReferable;

  public SingletonScope(Referable referable) {
    myReferable = referable;
  }

  @Override
  public List<Referable> getElements() {
    return Collections.singletonList(myReferable);
  }

  @Override
  public Referable resolveName(String name) {
    return myReferable.textRepresentation().equals(name) ? myReferable : null;
  }

  @Override
  public Collection<? extends Concrete.Instance> getInstances() {
    return Collections.emptyList();
  }
}
