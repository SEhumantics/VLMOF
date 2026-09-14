package org.vlmof.bridge;
import java.nio.file.Path;
import java.util.Map;
import java.nio.file.Files;
import java.security.MessageDigest;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.databind.node.ArrayNode;
import com.fasterxml.jackson.databind.node.ObjectNode;
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
 private static String sha(Path p)throws Exception{byte[] b=Files.readAllBytes(p);return java.util.HexFormat.of().formatHex(MessageDigest.getInstance("SHA-256").digest(b));}
 public static void main(String[] a) throws Exception { if(a.length!=4) throw new IllegalArgumentException("usage: StripEcoreAnnotations input.ecore adapted.ecore railway.xcore manifest.json"); String source=Files.readString(Path.of(a[2]));if(!source.contains("int ^id")||!source.contains("int length")||!source.contains("boolean active"))throw new IllegalArgumentException("REJECT Xcore primitive source basis mismatch"); var set=new ResourceSetImpl(); Resource.Factory.Registry.INSTANCE.getExtensionToFactoryMap().put("ecore",new EcoreResourceFactoryImpl()); Resource in=set.getResource(URI.createFileURI(Path.of(a[0]).toAbsolutePath().toString()),true); int n=0,ints=0,bools=0;ArrayNode changes=new ObjectMapper().createArrayNode(); for(EObject root:in.getContents()){ java.util.List<EObject> all=new java.util.ArrayList<>();all.add(root);TreeIterator<EObject> it=root.eAllContents();while(it.hasNext())all.add(it.next());for(EObject e:all){if(e instanceof EModelElement m){for(var an:m.getEAnnotations()){changes.addObject().put("kind","annotation").put("source",an.getSource()).put("details",an.getDetails().toString());}n+=m.getEAnnotations().size();m.getEAnnotations().clear();}if(e instanceof EAttribute x && x.getEAttributeType()==EcorePackage.Literals.EJAVA_OBJECT){String q=x.getEContainingClass().getName()+"."+x.getName();String target;if("Route.active".equals(q)){x.setEType(EcorePackage.Literals.EBOOLEAN);bools++;target="EBoolean";}else if("RailwayElement.id".equals(q)||"Segment.length".equals(q)){x.setEType(EcorePackage.Literals.EINT);ints++;target="EInt";}else throw new IllegalArgumentException("REJECT unclassified EJavaObject attribute "+q);changes.addObject().put("kind","datatype").put("attribute",q).put("old","EJavaObject").put("new",target);}}} if(n!=1||ints!=2||bools!=1)throw new IllegalArgumentException("REJECT unexpected Train adaptation counts"); Resource out=set.createResource(URI.createFileURI(Path.of(a[1]).toAbsolutePath().toString())); out.getContents().addAll(in.getContents());out.save(Map.of());ObjectNode manifest=new ObjectMapper().createObjectNode();manifest.put("kind","train-xcore-profile-adaptation-v1").put("inputSha256",sha(Path.of(a[0]))).put("outputSha256",sha(Path.of(a[1]))).put("xcoreSha256",sha(Path.of(a[2]))).put("sourceBasis","RailwayElement.id:int; Segment.length:int; Route.active:boolean").set("changes",changes);new ObjectMapper().writerWithDefaultPrettyPrinter().writeValue(Path.of(a[3]).toFile(),manifest);System.out.println("ADAPTED_ECORE removedAnnotations="+n+" eJavaObjectToEInt="+ints+" eJavaObjectToEBoolean="+bools); }
}
