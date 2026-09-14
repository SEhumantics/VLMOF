package org.vlmof.bridge;
import java.nio.file.Path;
import java.util.Map;
import org.eclipse.emf.common.util.TreeIterator;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.EPackage;
import org.eclipse.emf.ecore.EModelElement;
import org.eclipse.emf.ecore.EAttribute;
import org.eclipse.emf.ecore.EcorePackage;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl;
import org.eclipse.emf.ecore.xmi.impl.EcoreResourceFactoryImpl;
/** Explicit profile adaptation: removes Ecore annotations from a separately named copy. */
public final class StripEcoreAnnotations {
 public static void main(String[] a) throws Exception { if(a.length!=2) throw new IllegalArgumentException("usage: StripEcoreAnnotations input.ecore adapted.ecore"); var set=new ResourceSetImpl(); Resource.Factory.Registry.INSTANCE.getExtensionToFactoryMap().put("ecore",new EcoreResourceFactoryImpl()); Resource in=set.getResource(URI.createFileURI(Path.of(a[0]).toAbsolutePath().toString()),true); int n=0,ints=0,bools=0; for(EObject root:in.getContents()){ java.util.List<EObject> all=new java.util.ArrayList<>();all.add(root);TreeIterator<EObject> it=root.eAllContents();while(it.hasNext())all.add(it.next());for(EObject e:all){if(e instanceof EModelElement m){n+=m.getEAnnotations().size();m.getEAnnotations().clear();}if(e instanceof EAttribute x && x.getEAttributeType()==EcorePackage.Literals.EJAVA_OBJECT){String q=x.getEContainingClass().getName()+"."+x.getName();if("Route.active".equals(q)){x.setEType(EcorePackage.Literals.EBOOLEAN);bools++;}else if("RailwayElement.id".equals(q)||"Segment.length".equals(q)){x.setEType(EcorePackage.Literals.EINT);ints++;}else throw new IllegalArgumentException("REJECT unclassified EJavaObject attribute "+q);}}} Resource out=set.createResource(URI.createFileURI(Path.of(a[1]).toAbsolutePath().toString())); out.getContents().addAll(in.getContents());out.save(Map.of());System.out.println("ADAPTED_ECORE removedAnnotations="+n+" eJavaObjectToEInt="+ints+" eJavaObjectToEBoolean="+bools); }
}
