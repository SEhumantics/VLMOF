package org.vlmof.bridge;
import java.nio.file.Path;
import java.util.List;
/** Executable boundary probe for the closed resource manifest. */
public final class ClosedManifestProbe {
 public static void main(String[] a){if(a.length!=2)throw new IllegalArgumentException("usage: ClosedManifestProbe allowed denied");var set=new ClosedManifestResourceSet(List.of(Path.of(a[0])));set.getResourceFactoryRegistry().getExtensionToFactoryMap().put("ecore",new org.eclipse.emf.ecore.xmi.impl.EcoreResourceFactoryImpl());set.loadManifest(Path.of(a[0]));try{set.getResource(org.eclipse.emf.common.util.URI.createFileURI(Path.of(a[1]).toAbsolutePath().toString()),true);throw new IllegalStateException("external load unexpectedly allowed");}catch(IllegalArgumentException expected){if(!expected.getMessage().contains("explicit manifest closure"))throw expected;}System.out.println("CLOSED_MANIFEST OK");}
}
