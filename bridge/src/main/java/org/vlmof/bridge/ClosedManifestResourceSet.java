package org.vlmof.bridge;

import java.nio.file.Path;
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl;

/** A ResourceSet whose demand loading is closed over an explicit file manifest.
 * Built-in Ecore classifiers are supplied through the package registry, not loaded. */
public final class ClosedManifestResourceSet extends ResourceSetImpl {
  private final Set<URI> allowed = new HashSet<>();
  public ClosedManifestResourceSet(Collection<Path> manifest) {
    for (Path p : manifest) allowed.add(URI.createFileURI(p.toAbsolutePath().normalize().toString()));
  }
  public boolean permits(URI uri) { return allowed.contains(uri); }
  @Override public Resource getResource(URI uri, boolean loadOnDemand) {
    if (org.eclipse.emf.ecore.EcorePackage.eNS_URI.equals(uri.toString())) return org.eclipse.emf.ecore.EcorePackage.eINSTANCE.eResource();
    if (loadOnDemand && !permits(uri)) throw new IllegalArgumentException("REJECT resource outside explicit manifest closure: " + uri);
    return super.getResource(uri, loadOnDemand);
  }
  /** Load only a manifest member; callers should register all EPackages before XMI. */
  public Resource loadManifest(Path path) {
    URI uri=URI.createFileURI(path.toAbsolutePath().normalize().toString());
    if(!allowed.contains(uri)) throw new IllegalArgumentException("REJECT resource not in explicit manifest: "+uri);
    return super.getResource(uri,true);
  }
}
