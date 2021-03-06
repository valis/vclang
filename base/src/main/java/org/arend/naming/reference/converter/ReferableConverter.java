package org.arend.naming.reference.converter;

import org.arend.naming.reference.LocatedReferable;
import org.arend.naming.reference.Referable;
import org.arend.naming.reference.TCReferable;

public interface ReferableConverter {
  TCReferable toDataLocatedReferable(LocatedReferable referable);

  default Referable convert(Referable referable) {
    return referable instanceof LocatedReferable ? toDataLocatedReferable((LocatedReferable) referable) : referable;
  }
}
