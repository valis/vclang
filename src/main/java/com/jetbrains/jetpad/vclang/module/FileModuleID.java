package com.jetbrains.jetpad.vclang.module;


import com.jetbrains.jetpad.vclang.module.utils.FileOperations;

import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

public class FileModuleID implements SerializableModuleID {
  private final ModulePath myModulePath;

  public FileModuleID(ModulePath modulePath) {
    myModulePath = modulePath;
  }

  @Override
  public ModulePath getModulePath() {
    return myModulePath;
  }

  @Override
  public void serialize(DataOutputStream stream) throws IOException {
    String[] path = myModulePath.list();
    stream.writeInt(path.length);
    for (String str : path) {
      stream.writeUTF(str);
    }
  }

  @Override
  public FileModuleID deserialize(DataInputStream stream) throws IOException {
    int pathSize = stream.readInt();
    List<String> path = new ArrayList<>(pathSize);
    for (int i = 0; i < pathSize; i++) {
      path.add(stream.readUTF());
    }
    return new FileModuleID(new ModulePath(path));
  }

  @Override
  public boolean equals(Object o) {
    return o == this || o instanceof FileModuleID && ((FileModuleID) o).myModulePath.equals(myModulePath);
  }

  @Override
  public int hashCode() {
    return myModulePath.hashCode();
  }

  @Override
  public String toString() {
    return FileOperations.getFile(new File("."), myModulePath, "{" + FileOperations.EXTENSION + "," + FileOperations.SERIALIZED_EXTENSION + "}").toString();
  }
}
