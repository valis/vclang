package org.arend.core.definition;

import org.arend.core.context.binding.Binding;
import org.arend.core.context.param.DependentLink;
import org.arend.core.expr.*;
import org.arend.core.sort.Level;
import org.arend.core.sort.Sort;
import org.arend.core.subst.ExprSubstitution;
import org.arend.core.subst.LevelPair;
import org.arend.core.subst.SubstVisitor;
import org.arend.ext.core.definition.CoreClassDefinition;
import org.arend.ext.core.definition.CoreClassField;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.naming.reference.TCDefReferable;
import org.arend.util.Pair;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.*;

public class ClassDefinition extends Definition implements CoreClassDefinition {
  private final Set<ClassDefinition> mySuperClasses = new LinkedHashSet<>();
  private final LinkedHashSet<ClassField> myFields = new LinkedHashSet<>();
  private final List<ClassField> myPersonalFields = new ArrayList<>();
  private final Map<ClassField, AbsExpression> myImplemented = new HashMap<>();
  private final Map<ClassField, AbsExpression> myDefaults = new HashMap<>();
  private final Map<ClassField, Set<ClassField>> myDefaultDependencies = new HashMap<>();
  private final Map<ClassField, Set<ClassField>> myDefaultImplDependencies = new HashMap<>();
  private final Map<ClassField, PiExpression> myOverridden = new HashMap<>();
  private ClassField myCoercingField;
  private Sort mySort = Sort.PROP;
  private boolean myRecord = false;
  private final CoerceData myCoerce = new CoerceData(this);
  private Set<ClassField> myGoodThisFields = Collections.emptySet();
  private Set<ClassField> myTypeClassParameters = Collections.emptySet();
  private final ParametersLevels<ParametersLevel> myParametersLevels = new ParametersLevels<>();
  private FunctionDefinition mySquasher;

  public ClassDefinition(TCDefReferable referable) {
    super(referable, TypeCheckingStatus.NEEDS_TYPE_CHECKING);
  }

  @Override
  public boolean isRecord() {
    return myRecord;
  }

  public void setRecord() {
    myRecord = true;
  }

  @Override
  public ClassField getClassifyingField() {
    return myCoercingField;
  }

  public void setClassifyingField(ClassField coercingField) {
    myCoercingField = coercingField;
  }

  public static class ParametersLevel extends org.arend.core.definition.ParametersLevel {
    public final List<ClassField> fields;
    public final List<Pair<ClassDefinition,Set<ClassField>>> strictList;

    public ParametersLevel(DependentLink parameters, int level, List<ClassField> fields, List<Pair<ClassDefinition,Set<ClassField>>> strictList) {
      super(parameters, level);
      this.fields = fields;
      this.strictList = strictList;
    }

    @Override
    public boolean hasEquivalentDomain(org.arend.core.definition.ParametersLevel another) {
      return another instanceof ParametersLevel && fields.equals(((ParametersLevel) another).fields) && super.hasEquivalentDomain(another);
    }

    private boolean checkExpressionsTypesStrict(List<Expression> expressions) {
      if (strictList == null || expressions.size() != strictList.size()) {
        return false;
      }
      for (int i = 0; i < expressions.size(); i++) {
        if (strictList.get(i) == null) {
          continue;
        }
        Expression type = expressions.get(i).getType();
        if (type == null) {
          return false;
        }
        ClassCallExpression classCall = type.cast(ClassCallExpression.class);
        if (classCall == null || !classCall.getDefinition().isSubClassOf(strictList.get(i).proj1)) {
          return false;
        }
        for (ClassField field : strictList.get(i).proj2) {
          if (!classCall.isImplemented(field)) {
            return false;
          }
        }
      }
      return true;
    }
  }

  @Override
  public List<? extends ParametersLevel> getParametersLevels() {
    return myParametersLevels.getList();
  }

  public void addParametersLevel(ParametersLevel parametersLevel) {
    myParametersLevels.add(parametersLevel);
  }

  public FunctionDefinition getSquasher() {
    return mySquasher;
  }

  public void setSquasher(FunctionDefinition squasher) {
    mySquasher = squasher;
  }

  public Integer getUseLevel(Map<ClassField,Expression> implemented, Binding thisBinding, boolean isStrict) {
    loop:
    for (ParametersLevel parametersLevel : myParametersLevels.getList()) {
      if (isStrict && parametersLevel.strictList == null || parametersLevel.fields.size() != implemented.size()) {
        continue;
      }
      List<Expression> expressions = new ArrayList<>();
      for (ClassField field : parametersLevel.fields) {
        Expression expr = implemented.get(field);
        if (expr == null || expr.findBinding(thisBinding)) {
          continue loop;
        }
        expressions.add(expr);
      }

      if (isStrict ? parametersLevel.checkExpressionsTypesStrict(expressions) : parametersLevel.checkExpressionsTypes(expressions)) {
        return parametersLevel.level;
      }
    }
    return null;
  }

  public Sort computeSort(LevelPair levels, Map<ClassField,Expression> implemented, Binding thisBinding) {
    Integer hLevel = getUseLevel(implemented, thisBinding, true);
    if (hLevel != null && hLevel == -1) {
      return Sort.PROP;
    }

    ClassCallExpression thisClass = new ClassCallExpression(this, levels, Collections.emptyMap(), mySort.subst(levels), getUniverseKind());
    Sort sort = Sort.PROP;

    for (ClassField field : myFields) {
      if (myImplemented.containsKey(field) || implemented.containsKey(field)) {
        continue;
      }

      PiExpression fieldType = getFieldType(field, levels);
      if (fieldType.getCodomain().isInstance(ErrorExpression.class)) {
        continue;
      }

      Expression type = fieldType
        .applyExpression(new ReferenceExpression(ExpressionFactory.parameter("this", thisClass)))
        .normalize(NormalizationMode.WHNF)
        .getType();
      Sort sort1 = type == null ? null : type.toSort();
      if (sort1 != null) {
        sort = sort.max(sort1);
      }
    }

    return hLevel == null ? sort : new Sort(sort.getPLevel(), new Level(hLevel));
  }

  public void updateSort() {
    mySort = computeSort(LevelPair.STD, Collections.emptyMap(), null);
  }

  @NotNull
  @Override
  public Sort getSort() {
    return mySort;
  }

  public void setSort(Sort sort) {
    mySort = sort;
  }

  @Override
  public CoerceData getCoerceData() {
    return myCoerce;
  }

  public static boolean isSubClassOf(ArrayDeque<CoreClassDefinition> classDefs, CoreClassDefinition classDef) {
    Set<CoreClassDefinition> visited = new HashSet<>();
    while (!classDefs.isEmpty()) {
      CoreClassDefinition subClass = classDefs.pop();
      if (!visited.add(subClass)) {
        continue;
      }
      if (subClass == classDef) {
        return true;
      }
      classDefs.addAll(subClass.getSuperClasses());
    }
    return false;
  }

  @Override
  public boolean isSubClassOf(@NotNull CoreClassDefinition classDefinition) {
    if (this.equals(classDefinition)) return true;
    ArrayDeque<CoreClassDefinition> classDefs = new ArrayDeque<>(mySuperClasses);
    return isSubClassOf(classDefs, classDefinition);
  }

  @NotNull
  @Override
  public Set<? extends ClassDefinition> getSuperClasses() {
    return mySuperClasses;
  }

  public void addSuperClass(ClassDefinition superClass) {
    mySuperClasses.add(superClass);
  }

  @NotNull
  @Override
  public Set<? extends ClassField> getFields() {
    return myFields;
  }

  @NotNull
  @Override
  public List<? extends ClassField> getPersonalFields() {
    return myPersonalFields;
  }

  public int getNumberOfNotImplementedFields() {
    return myFields.size() - myImplemented.size();
  }

  public void addField(ClassField field) {
    myFields.add(field);
  }

  public void addPersonalField(ClassField field) {
    myPersonalFields.add(field);
  }

  public void addFields(Collection<? extends ClassField> fields) {
    myFields.addAll(fields);
  }

  @Override
  public boolean isImplemented(@NotNull CoreClassField field) {
    return field instanceof ClassField && myImplemented.containsKey(field);
  }

  @NotNull
  @Override
  public Set<Map.Entry<ClassField, AbsExpression>> getImplemented() {
    return myImplemented.entrySet();
  }

  public Set<? extends ClassField> getImplementedFields() {
    return myImplemented.keySet();
  }

  @Override
  public AbsExpression getImplementation(@NotNull CoreClassField field) {
    return field instanceof ClassField ? myImplemented.get(field) : null;
  }

  public AbsExpression implementField(ClassField field, AbsExpression impl) {
    return myImplemented.putIfAbsent(field, impl);
  }

  public Set<Map.Entry<ClassField, AbsExpression>> getDefaults() {
    return myDefaults.entrySet();
  }

  public AbsExpression getDefault(@NotNull CoreClassField field) {
    return field instanceof ClassField ? myDefaults.get(field) : null;
  }

  public AbsExpression addDefault(ClassField field, AbsExpression impl) {
    return myDefaults.put(field, impl);
  }

  public AbsExpression addDefaultIfAbsent(ClassField field, AbsExpression impl) {
    return myDefaults.putIfAbsent(field, impl);
  }

  public Map<ClassField, Set<ClassField>> getDefaultDependencies() {
    return myDefaultDependencies;
  }

  public void addDefaultDependencies(ClassField field, Set<ClassField> dependencies) {
    myDefaultDependencies.computeIfAbsent(field, k -> new HashSet<>()).addAll(dependencies);
  }

  public void addDefaultDependency(ClassField field, ClassField dependency) {
    myDefaultDependencies.computeIfAbsent(field, k -> new HashSet<>()).add(dependency);
  }

  public Map<ClassField, Set<ClassField>> getDefaultImplDependencies() {
    return myDefaultImplDependencies;
  }

  public void addDefaultImplDependencies(ClassField field, Set<ClassField> dependencies) {
    myDefaultImplDependencies.computeIfAbsent(field, k -> new HashSet<>()).addAll(dependencies);
  }

  public void addDefaultImplDependency(ClassField field, ClassField dependency) {
    myDefaultImplDependencies.computeIfAbsent(field, k -> new HashSet<>()).add(dependency);
  }

  public void removeDefault(ClassField field) {
    myDefaults.remove(field);
    myDefaultDependencies.remove(field);
  }

  @NotNull
  @Override
  public Set<Map.Entry<ClassField, PiExpression>> getOverriddenFields() {
    return myOverridden.entrySet();
  }

  public PiExpression getOverriddenType(ClassField field, LevelPair levels) {
    PiExpression type = myOverridden.get(field);
    return type == null || levels.isSTD() ? type : (PiExpression) new SubstVisitor(new ExprSubstitution(), levels).visitPi(type, null);
  }

  public PiExpression getFieldType(ClassField field) {
    PiExpression type = myOverridden.get(field);
    return type == null ? field.getType(LevelPair.STD) : type;
  }

  public PiExpression getFieldType(ClassField field, LevelPair levels) {
    PiExpression type = myOverridden.get(field);
    return type == null ? field.getType(levels) : levels.isSTD() ? type : (PiExpression) new SubstVisitor(new ExprSubstitution(), levels).visitPi(type, null);
  }

  public Expression getFieldType(ClassField field, LevelPair levels, Expression thisExpr) {
    PiExpression type = myOverridden.get(field);
    if (type == null) {
      type = field.getType(LevelPair.STD);
    }
    return type.getCodomain().subst(new ExprSubstitution(type.getParameters(), thisExpr), levels);
  }

  @Nullable
  @Override
  public PiExpression getOverriddenType(@NotNull CoreClassField field) {
    return field instanceof ClassField ? myOverridden.get(field) : null;
  }

  @Override
  public CoreClassField findField(@NotNull String name) {
    for (ClassField field : getFields()) {
      if (field.getName().equals(name)) {
        return field;
      }
    }
    return null;
  }

  @Override
  public boolean isOverridden(@NotNull CoreClassField field) {
    return field instanceof ClassField && myOverridden.containsKey(field);
  }

  public PiExpression overrideField(ClassField field, PiExpression type) {
    return myOverridden.putIfAbsent(field, type);
  }

  public Set<? extends ClassField> getGoodThisFields() {
    return myGoodThisFields;
  }

  public boolean isGoodField(ClassField field) {
    return myGoodThisFields.contains(field);
  }

  public void setGoodThisFields(Set<ClassField> goodThisFields) {
    myGoodThisFields = goodThisFields;
  }

  public Set<? extends ClassField> getTypeClassFields() {
    return myTypeClassParameters;
  }

  public boolean isTypeClassField(ClassField field) {
    return myTypeClassParameters.contains(field);
  }

  public void setTypeClassFields(Set<ClassField> typeClassFields) {
    myTypeClassParameters = typeClassFields;
  }

  @Override
  public Expression getTypeWithParams(List<? super DependentLink> params, LevelPair levels) {
    return new UniverseExpression(mySort.subst(levels));
  }

  @Override
  public ClassCallExpression getDefCall(LevelPair levels, List<Expression> args) {
    return new ClassCallExpression(this, levels, Collections.emptyMap(), mySort.subst(levels), getUniverseKind());
  }

  public void clear() {
    mySuperClasses.clear();
    myFields.clear();
    myPersonalFields.clear();
    myImplemented.clear();
    myOverridden.clear();
    myCoercingField = null;
  }

  @Override
  public void fill() {
    for (ClassField field : myPersonalFields) {
      field.fill();
    }
  }
}
