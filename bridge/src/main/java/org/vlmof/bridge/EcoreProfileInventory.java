package org.vlmof.bridge;

import java.nio.file.Path;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.common.util.TreeIterator;
import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.EClassifier;
import org.eclipse.emf.ecore.EDataType;
import org.eclipse.emf.ecore.EEnum;
import org.eclipse.emf.ecore.EGenericType;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.EReference;
import org.eclipse.emf.ecore.EOperation;
import org.eclipse.emf.ecore.EStructuralFeature;
import org.eclipse.emf.ecore.ETypeParameter;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.ResourceSet;
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl;
import org.eclipse.emf.ecore.xmi.impl.EcoreResourceFactoryImpl;

/** Reports source features that make an original Ecore package outside E1's profile. */
public final class EcoreProfileInventory {
  private static boolean primitive(EDataType type) {
    String n = type.getName();
    return type.getEPackage() != null
        && "http://www.eclipse.org/emf/2002/Ecore".equals(type.getEPackage().getNsURI())
        && ("EBoolean".equals(n) || "EInt".equals(n) || "EString".equals(n));
  }

  private static void reject(String kind, String where) {
    System.out.printf("REJECT %s %s%n", kind, where);
  }

  public static void main(String[] args) {
    if (args.length != 1) throw new IllegalArgumentException("usage: EcoreProfileInventory FILE.ecore");
    Resource.Factory.Registry.INSTANCE.getExtensionToFactoryMap().put("ecore", new EcoreResourceFactoryImpl());
    ResourceSet set = new ResourceSetImpl();
    Resource resource = set.getResource(URI.createFileURI(Path.of(args[0]).toAbsolutePath().toString()), true);
    int rejected = 0;
    TreeIterator<EObject> contents = resource.getAllContents();
    while (contents.hasNext()) {
      EObject item = contents.next();
      if (item instanceof EOperation operation) { reject("operation", operation.getName()); rejected++; }
      if (item instanceof ETypeParameter parameter) { reject("generic-type-parameter", parameter.getName()); rejected++; }
      if (item instanceof EStructuralFeature feature) {
        if (feature.isDerived()) { reject("derived-feature", feature.getName()); rejected++; }
        if (feature.isTransient()) { reject("transient-feature", feature.getName()); rejected++; }
        if (feature.isVolatile()) { reject("volatile-feature", feature.getName()); rejected++; }
        if (!feature.isChangeable()) { reject("read-only-feature", feature.getName()); rejected++; }
        if (feature.isUnsettable()) { reject("unsettable-feature", feature.getName()); rejected++; }
        if (feature.getDefaultValueLiteral() != null) { reject("default-value-literal", feature.getName()); rejected++; }
        if (feature instanceof EReference reference && reference.getEType() != null
            && reference.getEType().getEPackage() != null
            && reference.getEType().getEPackage() != feature.getEContainingClass().getEPackage()) {
          reject("external-reference-classifier", feature.getName() + ":" + reference.getEType().getName()); rejected++;
        }
      }
      if (item instanceof EDataType data && !(data instanceof EEnum) && !primitive(data)) {
        reject("custom-or-unsupported-datatype", data.getName()); rejected++;
      }
      if (item instanceof EGenericType generic && !generic.getETypeArguments().isEmpty()) {
        String classifier = generic.getEClassifier() == null ? "unresolved" : generic.getEClassifier().getName();
        reject("generic-type-arguments", classifier + " arity=" + generic.getETypeArguments().size()); rejected++;
      }
      if (item instanceof EClass clazz && !clazz.getEGenericSuperTypes().isEmpty()) { reject("generic-supertype", clazz.getName()); rejected++; }
      if (item instanceof EClassifier classifier && classifier.getEPackage() == null) { reject("unowned-classifier", classifier.getName()); rejected++; }
    }
    System.out.printf("INVENTORY file=%s rejected-features=%d%n", args[0], rejected);
  }
}
