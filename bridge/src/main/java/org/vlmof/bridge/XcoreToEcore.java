package org.vlmof.bridge;

import com.google.inject.Injector;
import java.nio.file.Path;
import java.util.Map;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.EPackage;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.ResourceSet;
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl;
import org.eclipse.emf.ecore.xcore.XPackage;
import org.eclipse.emf.ecore.xcore.XcoreStandaloneSetup;
import org.eclipse.emf.ecore.xcore.mappings.XcoreMapper;
import org.eclipse.emf.ecore.xmi.impl.EcoreResourceFactoryImpl;

/** Compiles the pinned Xcore source into an Ecore resource through Xcore itself. */
public final class XcoreToEcore {
  public static void main(String[] args) throws Exception {
    if (args.length != 2) throw new IllegalArgumentException("usage: XcoreToEcore railway.xcore railway.ecore");
    Injector injector = new XcoreStandaloneSetup().createInjectorAndDoEMFRegistration();
    ResourceSet set = new ResourceSetImpl();
    Resource input = set.getResource(URI.createFileURI(Path.of(args[0]).toAbsolutePath().toString()), true);
    XPackage pkg = null; for (org.eclipse.emf.ecore.EObject item : input.getContents()) if (item instanceof XPackage candidate) { pkg = candidate; break; }
    if (pkg == null) throw new IllegalArgumentException("Xcore load failed contents=" + input.getContents().size() + " errors=" + input.getErrors());
    EPackage ecore = injector.getInstance(XcoreMapper.class).getMapping(pkg).getEPackage();
    Resource.Factory.Registry.INSTANCE.getExtensionToFactoryMap().put("ecore", new EcoreResourceFactoryImpl());
    Resource output = set.createResource(URI.createFileURI(Path.of(args[1]).toAbsolutePath().toString())); output.getContents().add(ecore); output.save(Map.of());
    System.out.printf("XCORE_COMPILED name=%s classifiers=%d nsURI=%s%n", ecore.getName(), ecore.getEClassifiers().size(), ecore.getNsURI());
  }
}
