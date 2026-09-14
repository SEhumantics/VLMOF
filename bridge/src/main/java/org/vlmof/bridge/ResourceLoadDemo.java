package org.vlmof.bridge;

import java.net.URL;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.EPackage;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.ResourceSet;
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl;
import org.eclipse.emf.ecore.xmi.impl.EcoreResourceFactoryImpl;
import org.eclipse.emf.ecore.xmi.impl.XMIResourceFactoryImpl;

/** Loads authored Ecore and XMI only; it deliberately performs no Core decoding. */
public final class ResourceLoadDemo {
  private static URI classpathUri(String name) throws Exception {
    URL resource = ResourceLoadDemo.class.getResource(name);
    if (resource == null) throw new IllegalStateException("missing classpath resource: " + name);
    return URI.createURI(resource.toURI().toString());
  }

  public static void main(String[] args) throws Exception {
    Resource.Factory.Registry registry = Resource.Factory.Registry.INSTANCE;
    registry.getExtensionToFactoryMap().put("ecore", new EcoreResourceFactoryImpl());
    registry.getExtensionToFactoryMap().put("xmi", new XMIResourceFactoryImpl());
    ResourceSet set = new ResourceSetImpl();

    Resource ecore = set.getResource(classpathUri("/samples/tiny.ecore"), true);
    EPackage pkg = (EPackage) ecore.getContents().getFirst();
    set.getPackageRegistry().put(pkg.getNsURI(), pkg);
    Resource xmi = set.getResource(classpathUri("/samples/tiny.xmi"), true);
    EObject root = xmi.getContents().getFirst();
    int children = ((java.util.List<?>) root.eGet(root.eClass().getEStructuralFeature("children"))).size();
    System.out.printf("LOADED nsURI=%s root=%s children=%d%n", pkg.getNsURI(),
        root.eClass().getName(), children);
  }
}
