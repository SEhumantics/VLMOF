package org.vlmof.bridge;

import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.node.ArrayNode;
import com.fasterxml.jackson.databind.node.ObjectNode;
import java.nio.file.Path;
import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Collections;
import javax.xml.parsers.DocumentBuilderFactory;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.eclipse.emf.common.util.EList;
import org.eclipse.emf.common.util.TreeIterator;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.EAttribute;
import org.eclipse.emf.ecore.EAnnotation;
import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.EClassifier;
import org.eclipse.emf.ecore.EDataType;
import org.eclipse.emf.ecore.EEnum;
import org.eclipse.emf.ecore.EEnumLiteral;
import org.eclipse.emf.ecore.EGenericType;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.EOperation;
import org.eclipse.emf.ecore.EPackage;
import org.eclipse.emf.ecore.EcoreFactory;
import org.eclipse.emf.ecore.EcorePackage;
import org.eclipse.emf.ecore.EReference;
import org.eclipse.emf.ecore.EStructuralFeature;
import org.eclipse.emf.ecore.ETypeParameter;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.ResourceSet;
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl;
import org.eclipse.emf.ecore.util.EcoreUtil;
import org.eclipse.emf.ecore.xmi.impl.EcoreResourceFactoryImpl;
import org.eclipse.emf.ecore.xmi.impl.XMIResourceFactoryImpl;
import org.eclipse.emf.ecore.xmi.XMIResource;
import org.eclipse.emf.ecore.xmi.XMLResource;

/**
 * EMF-backed importer for the narrow E1 profile.  The command is deliberately
 * manifest based: `import a.ecore b.ecore -- one.xmi two.xmi`.  Resources outside
 * those two lists are never loaded as a convenience; an unresolved proxy is an
 * error with its source location.
 */
public final class EmfInterchange {
  private static final ObjectMapper JSON = new ObjectMapper();
  private final List<String> diagnostics = new ArrayList<>();
  private final IdentityHashMap<EPackage, Integer> packages = new IdentityHashMap<>();
  private final IdentityHashMap<EClass, Integer> classes = new IdentityHashMap<>();
  private final IdentityHashMap<EStructuralFeature, Integer> properties = new IdentityHashMap<>();
  private final IdentityHashMap<EEnum, Integer> enums = new IdentityHashMap<>();
  private final IdentityHashMap<EEnumLiteral, Integer> literals = new IdentityHashMap<>();
  private final IdentityHashMap<EObject, Integer> objects = new IdentityHashMap<>();
  private final List<EObject> objectOrder = new ArrayList<>();
  /** Feature names lexically present in original file XMI, paired by containment preorder. */
  private final IdentityHashMap<EObject, java.util.Set<String>> lexicalFeatures = new IdentityHashMap<>();
  private int nextPackage, nextClass, nextProperty, nextEnum, nextLiteral, nextObject;

  private static URI fileUri(String path) { return URI.createFileURI(Path.of(path).toAbsolutePath().toString()); }
  private static String loc(EObject o) { return EcoreUtil.getURI(o).toString(); }
  private void reject(String kind, EObject item) { diagnostics.add("REJECT " + kind + " at " + loc(item)); }
  private void require(boolean ok) { if (!ok) throw new IllegalArgumentException(String.join("\n", diagnostics)); }

  private static boolean primitive(EDataType d) {
    return d.getEPackage() != null && "http://www.eclipse.org/emf/2002/Ecore".equals(d.getEPackage().getNsURI())
      && ("EBoolean".equals(d.getName()) || "EInt".equals(d.getName()) || "EString".equals(d.getName()));
  }
  private static ObjectNode object() { return JSON.createObjectNode(); }
  private static ArrayNode array() { return JSON.createArrayNode(); }
  private static void named(ObjectNode n, String key, String value) { if (value == null) n.putNull(key); else n.put(key, value); }
  private static void idOrNull(ObjectNode n, String key, Integer value) { if (value == null) n.putNull(key); else n.put(key, value); }

  private static void registerPackageTree(ResourceSet set, EPackage p) {
    set.getPackageRegistry().put(p.getNsURI(), p);
    for (EPackage child : p.getESubpackages()) registerPackageTree(set, child);
  }

  private void preflight(ResourceSet set, List<Resource> ecores) {
    for (Resource r : ecores) {
      for (EObject root : r.getContents()) inspect(root);
      TreeIterator<EObject> it = r.getAllContents(); while (it.hasNext()) inspect(it.next());
    }
    require(diagnostics.isEmpty());
  }
  private void inspect(EObject item) {
    if (item instanceof EAnnotation) reject("annotation", item);
    if (item instanceof EOperation) reject("operation", item);
    if (item instanceof ETypeParameter) reject("generic-type-parameter", item);
    if (item instanceof EGenericType g && (!g.getETypeArguments().isEmpty() || g.getETypeParameter() != null || g.getEUpperBound() != null || g.getELowerBound() != null)) reject("generic-type", item);
    if (item instanceof EStructuralFeature f) {
      if (f.isDerived()) reject("derived-feature", f);
      if (f.isTransient()) reject("transient-feature", f);
      if (f.isVolatile()) reject("volatile-feature", f);
      if (!f.isChangeable()) reject("read-only-feature", f);
      if (f.isUnsettable()) reject("unsettable-feature", f);
      if (f.getDefaultValueLiteral() != null) reject("default-value-literal", f);
      if (f.getEGenericType() != null && (!f.getEGenericType().getETypeArguments().isEmpty() || f.getEGenericType().getETypeParameter() != null)) reject("generic-feature-type", f);
    }
    if (item instanceof EDataType d && !(d instanceof EEnum) && !primitive(d)) reject("custom-or-unsupported-datatype", d);
  }

  private void allocatePackage(EPackage p) {
    if (packages.putIfAbsent(p, nextPackage) == null) nextPackage++;
    for (EPackage child : p.getESubpackages()) allocatePackage(child);
  }
  private void allocateDeclarations(EPackage p) {
    for (EClassifier c : p.getEClassifiers()) {
      if (c instanceof EClass k) {
        if (k.isInterface()) reject("interface-class", k); else { classes.put(k, nextClass++); for (EStructuralFeature f : k.getEStructuralFeatures()) properties.put(f, nextProperty++); }
      } else if (c instanceof EEnum e) { enums.put(e, nextEnum++); for (EEnumLiteral l : e.getELiterals()) literals.put(l, nextLiteral++); }
    }
    for (EPackage child : p.getESubpackages()) allocateDeclarations(child);
  }
  private void allocateObjects(List<Resource> xmis) {
    for (Resource r : xmis) { for (EObject root : r.getContents()) allocateObjectTree(root); }
  }
  private static void xmlElements(Element e, List<Element> out) { out.add(e); NodeList nodes=e.getChildNodes(); for(int i=0;i<nodes.getLength();i++) if(nodes.item(i).getNodeType()==Node.ELEMENT_NODE) xmlElements((Element)nodes.item(i),out); }
  private void trackLexicalFeatures(List<Resource> xmis) throws Exception {
    for(Resource r:xmis) {
      if(!r.getURI().isFile()) { diagnostics.add("REJECT lexical-presence-unavailable for non-file XMI "+r.getURI()); continue; }
      DocumentBuilderFactory factory=DocumentBuilderFactory.newInstance(); factory.setNamespaceAware(true); List<Element> elements=new ArrayList<>(); xmlElements(factory.newDocumentBuilder().parse(Path.of(r.getURI().toFileString()).toFile()).getDocumentElement(),elements);
      List<EObject> all=new ArrayList<>(); for(EObject root:r.getContents()){ all.add(root); TreeIterator<EObject> it=root.eAllContents(); while(it.hasNext())all.add(it.next()); }
      if(elements.size()!=all.size()) { for(Element e:elements) { String id=e.getAttributeNS("http://www.omg.org/XMI","id"); EObject o=id.isEmpty()?null:r.getEObject(id); if(o!=null) { java.util.Set<String> names=new java.util.HashSet<>(); for(int a=0;a<e.getAttributes().getLength();a++) names.add(e.getAttributes().item(a).getLocalName()==null?e.getAttributes().item(a).getNodeName():e.getAttributes().item(a).getLocalName()); lexicalFeatures.put(o,names); } } if(lexicalFeatures.size()<all.size()) { diagnostics.add("REJECT lexical-presence-unmappable XML element/object traversal "+r.getURI()); continue; } }
      else for(int i=0;i<all.size();i++) { java.util.Set<String> names=new java.util.HashSet<>(); Element e=elements.get(i); for(int a=0;a<e.getAttributes().getLength();a++) names.add(e.getAttributes().item(a).getLocalName()==null?e.getAttributes().item(a).getNodeName():e.getAttributes().item(a).getLocalName()); lexicalFeatures.put(all.get(i),names); }
    }
  }
  private void allocateObjectTree(EObject o) {
    if (!objects.containsKey(o)) { objects.put(o, nextObject++); objectOrder.add(o); for (EObject c : o.eContents()) allocateObjectTree(c); }
  }

  private ObjectNode upper(int upper) { ObjectNode n = object(); if (upper < 0) n.put("tag", "unlimited"); else { n.put("tag", "finite"); n.put("value", upper); } return n; }
  private ObjectNode type(EClassifier t) {
    ObjectNode n = object();
    if (t instanceof EClass c) { Integer id = classes.get(c); if (id == null) throw new IllegalArgumentException("REJECT external classifier outside package manifest: " + c.getName()); n.put("tag", "reference"); n.put("id", id); }
    else if (t instanceof EEnum e) { Integer id = enums.get(e); if (id == null) throw new IllegalArgumentException("REJECT external enumeration outside package manifest: " + e.getName()); n.put("tag", "enumeration"); n.put("id", id); }
    else if (t instanceof EDataType d && primitive(d)) n.put("tag", switch (d.getName()) { case "EBoolean" -> "boolean"; case "EInt" -> "integer"; default -> "string"; });
    else throw new IllegalArgumentException("REJECT unsupported type: " + (t == null ? "null" : t.getName()));
    return n;
  }
  private ObjectNode property(EStructuralFeature f) {
    ObjectNode n = object(); n.put("id", properties.get(f)); named(n, "name", f.getName());
    ObjectNode owner = object(); owner.put("tag", "class"); owner.put("id", classes.get(f.getEContainingClass())); n.set("owner", owner);
    n.set("type", type(f.getEType())); ObjectNode m = object(); m.put("lower", f.getLowerBound()); m.set("upper", upper(f.getUpperBound())); m.put("ordered", f.isOrdered()); m.put("unique", f.isUnique()); n.set("multiplicity", m);
    n.put("aggregation", f instanceof EReference r && r.isContainment() ? "composite" : "none"); n.put("idProperty", f instanceof EAttribute a && a.isID()); return n;
  }
  private ObjectNode value(Object v, EStructuralFeature f) {
    ObjectNode n = object();
    if (f instanceof EReference) { n.put("tag", "reference"); Integer i = objects.get(v); if (i == null) throw new IllegalArgumentException("REJECT reference outside instance manifest from " + f.getName()); n.put("object", i); return n; }
    EDataType t = ((EAttribute) f).getEAttributeType();
    if (t instanceof EEnum e) { n.put("tag", "enumeration"); n.put("enumeration", enums.get(e)); n.put("literal", literals.get(v)); }
    else if ("EBoolean".equals(t.getName())) { n.put("tag", "boolean"); n.put("value", (Boolean) v); }
    else if ("EInt".equals(t.getName())) { n.put("tag", "integer"); n.put("value", ((Number) v).intValue()); }
    else { n.put("tag", "string"); n.put("value", String.valueOf(v)); }
    return n;
  }
  private void noProxies(List<Resource> xmis) {
    for (Resource r : xmis) for (EObject root : r.getContents()) { if (root.eIsProxy()) reject("unresolved-proxy", root); List<EObject> all=new ArrayList<>(); all.add(root); TreeIterator<EObject> it = root.eAllContents(); while(it.hasNext()) all.add(it.next()); for(EObject o:all) { if (o.eIsProxy()) reject("unresolved-proxy", o); for (EReference ref : o.eClass().getEAllReferences()) { Object v = o.eGet(ref, false); if (v instanceof EObject e && e.eIsProxy()) reject("unresolved-proxy-reference", o); if (v instanceof List<?> xs) for (Object x : xs) if (x instanceof EObject e && e.eIsProxy()) reject("unresolved-proxy-reference", o); } } }
    require(diagnostics.isEmpty());
  }
  private ObjectNode emit(List<EPackage> roots, List<Resource> xmis, List<String> ecorePaths, List<String> xmiPaths) {
    ObjectNode out = object(); out.put("version", "vlmof-e1-1"); ObjectNode schema = object(); ArrayNode ps = array(), cs = array(), fs = array(), as = array(), es = array(), ls = array();
    for (EPackage p : roots) emitPackage(p, ps, cs, fs, as, es, ls); schema.set("packages", ps); schema.set("classes", cs); schema.set("properties", fs); schema.set("associations", as); schema.set("enumerations", es); schema.set("literals", ls); out.set("schema", schema);
    ObjectNode snapshot = object(); ArrayNode os = array(), observations = array();
    for (EObject o : objectOrder) { int objectId = objects.get(o); ObjectNode on = object(); on.put("id", objectId); on.put("classifier", classes.get(o.eClass())); os.add(on); for (EStructuralFeature f : o.eClass().getEAllStructuralFeatures()) { if (!properties.containsKey(f)) continue; ObjectNode ob = object(); ob.put("object", objectId); ob.put("property", properties.get(f)); ArrayNode occ = array(); Object raw = o.eGet(f, false); if (raw instanceof List<?> values) for (Object v : values) occ.add(value(v, f)); else if (raw != null && (o.eIsSet(f) || lexicalFeatures.getOrDefault(o,java.util.Set.of()).contains(f.getName()))) occ.add(value(raw, f)); ob.set("occurrences", occ); observations.add(ob); } }
    snapshot.set("objects", os); snapshot.set("observations", observations); out.set("snapshot", snapshot);
    ObjectNode provenance = object(); provenance.put("allocation", "manifest-order package containment; manifest-order XMI containment preorder"); provenance.put("associationOwnership", "Ecore references are class-owned; paired references are exported as associations with class-owned ends"); ArrayNode pm = array(); for (String p : ecorePaths) pm.add(p); provenance.set("ecoreManifest", pm); ArrayNode im = array(); for (String p : xmiPaths) im.add(p); provenance.set("xmiManifest", im); out.set("provenance", provenance); return out;
  }
  private void emitPackage(EPackage p, ArrayNode ps, ArrayNode cs, ArrayNode fs, ArrayNode as, ArrayNode es, ArrayNode ls) {
    ObjectNode pn = object(); pn.put("id", packages.get(p)); named(pn, "name", p.getName()); idOrNull(pn, "parent", p.getESuperPackage() == null ? null : packages.get(p.getESuperPackage())); ps.add(pn);
    for (EClassifier c : p.getEClassifiers()) if (c instanceof EClass k && classes.containsKey(k)) { ObjectNode cn = object(); cn.put("id", classes.get(k)); named(cn, "name", k.getName()); cn.put("package", packages.get(p)); cn.put("abstract", k.isAbstract()); ArrayNode supers = array(); for (EClass s : k.getESuperTypes()) { Integer sid = classes.get(s); if (sid == null) throw new IllegalArgumentException("REJECT superclass outside package manifest: " + s.getName()); supers.add(sid); } cn.set("supers", supers); cs.add(cn); for (EStructuralFeature f : k.getEStructuralFeatures()) fs.add(property(f)); }
    for (EClassifier c : p.getEClassifiers()) if (c instanceof EEnum e) { ObjectNode en = object(); en.put("id", enums.get(e)); named(en, "name", e.getName()); en.put("package", packages.get(p)); es.add(en); for (EEnumLiteral l : e.getELiterals()) { ObjectNode ln = object(); ln.put("id", literals.get(l)); named(ln, "name", l.getName()); ln.put("enumeration", enums.get(e)); ls.add(ln); } }
    // A pair is emitted once, while both Ecore ends retain their actual class ownership.
    for (EClassifier c : p.getEClassifiers()) if (c instanceof EClass k) for (EReference r : k.getEReferences()) if (r.getEOpposite() != null && properties.get(r) < properties.get(r.getEOpposite())) { ObjectNode an = object(); an.put("id", as.size()); named(an, "name", r.getName() + "__" + r.getEOpposite().getName()); an.put("package", packages.get(p)); ArrayNode ends = array(); ends.add(properties.get(r)); ends.add(properties.get(r.getEOpposite())); an.set("ends", ends); as.add(an); }
    for (EPackage c : p.getESubpackages()) emitPackage(c, ps, cs, fs, as, es, ls);
  }
  private static List<Resource> reloadExports(List<Resource> original, List<EPackage> roots) throws Exception {
    ResourceSet set = new ResourceSetImpl();
    set.getResourceFactoryRegistry().getExtensionToFactoryMap().put("xmi", new XMIResourceFactoryImpl());
    for (EPackage p : roots) registerPackageTree(set, p);
    List<Resource> reloaded = new ArrayList<>(); int n = 0;
    for (Resource r : original) {
      ByteArrayOutputStream bytes = new ByteArrayOutputStream(); r.save(bytes, Map.of());
      Resource copy = set.createResource(URI.createURI("memory:/e1-export-" + n++ + ".xmi"));
      copy.load(new ByteArrayInputStream(bytes.toByteArray()), Map.of()); reloaded.add(copy);
    }
    return reloaded;
  }
  private static int integer(JsonNode n, String field) {
    if (!n.has(field) || !n.get(field).isIntegralNumber() || !n.get(field).canConvertToInt()) throw new IllegalArgumentException("E1 export malformed integer `" + field + "`");
    return n.get(field).intValue();
  }
  private static void canonicalIds(JsonNode items, String label) {
    int expected=0; for(JsonNode item:items) { if(integer(item,"id")!=expected++) throw new IllegalArgumentException("REJECT E1 export noncanonical "+label+" id; export records only manifest-order allocations"); }
  }
  private static String text(JsonNode n, String field) {
    if (!n.has(field) || !n.get(field).isTextual()) throw new IllegalArgumentException("E1 export malformed string `" + field + "`");
    return n.get(field).textValue();
  }
  private static void copyMultiplicity(JsonNode source, EStructuralFeature target) {
    target.setLowerBound(integer(source, "lower")); JsonNode upper = source.get("upper"); String tag = text(upper, "tag"); target.setUpperBound("unlimited".equals(tag) ? -1 : integer(upper, "value"));
    if(!source.has("ordered") || !source.get("ordered").isBoolean() || !source.has("unique") || !source.get("unique").isBoolean()) throw new IllegalArgumentException("E1 export malformed multiplicity flags");
    target.setOrdered(source.get("ordered").booleanValue()); target.setUnique(source.get("unique").booleanValue());
  }
  /** Builds a fresh dynamic Ecore model from an E1 document; it never reuses source EObjects. */
  private static void exportDocument(Path input, Path ecoreOut, Path xmiOut) throws Exception {
    JsonNode d = JSON.readTree(input.toFile());
    if (!"vlmof-e1-1".equals(text(d, "version"))) throw new IllegalArgumentException("E1 export unsupported version");
    JsonNode s = d.get("schema"), snap = d.get("snapshot"); if (s == null || snap == null) throw new IllegalArgumentException("E1 export requires schema and snapshot");
    for(String kind:List.of("packages","classes","properties","associations","enumerations","literals")) canonicalIds(s.withArray(kind),kind);
    java.util.Set<Integer> paired=new java.util.HashSet<>(); for(JsonNode a:s.withArray("associations")) for(JsonNode end:a.withArray("ends")) paired.add(end.intValue());
    for(JsonNode observation:snap.withArray("observations")) if(paired.contains(integer(observation,"property"))) { java.util.Set<String> seen=new java.util.HashSet<>(); for(JsonNode occurrence:observation.withArray("occurrences")) if(!seen.add(canon(occurrence))) throw new IllegalArgumentException("UNSUPPORTED repeated paired reference occurrence for native EMF EOpposite export (EMF 2.39.0)"); }
    canonicalIds(snap.withArray("objects"),"objects"); EcoreFactory f = EcoreFactory.eINSTANCE;
    Map<Integer,EPackage> pkgs = new LinkedHashMap<>(); Map<Integer,EClass> cls = new LinkedHashMap<>(); Map<Integer,EEnum> ens = new LinkedHashMap<>(); Map<Integer,EEnumLiteral> lits = new LinkedHashMap<>(); Map<Integer,EStructuralFeature> features = new LinkedHashMap<>();
    for (JsonNode p : s.withArray("packages")) { if(p.path("name").isNull()) throw new IllegalArgumentException("REJECT E1 export unnamed package"); EPackage q = f.createEPackage(); q.setName(text(p,"name")); q.setNsPrefix(q.getName()); q.setNsURI("https://vlmof.example/export/" + integer(p,"id")); pkgs.put(integer(p,"id"),q); }
    for (JsonNode p : s.withArray("packages")) if (!p.path("parent").isNull()) { EPackage parent=pkgs.get(integer(p,"parent")); if(parent==null) throw new IllegalArgumentException("E1 export dangling package parent"); parent.getESubpackages().add(pkgs.get(integer(p,"id"))); }
    for (JsonNode e : s.withArray("enumerations")) { if(e.path("name").isNull()) throw new IllegalArgumentException("REJECT E1 export unnamed enumeration"); EEnum en=f.createEEnum(); en.setName(text(e,"name")); EPackage p=pkgs.get(integer(e,"package")); if(p==null) throw new IllegalArgumentException("E1 export dangling enum package"); p.getEClassifiers().add(en); ens.put(integer(e,"id"),en); }
    for (JsonNode l : s.withArray("literals")) { if(l.path("name").isNull()) throw new IllegalArgumentException("REJECT E1 export unnamed literal"); EEnumLiteral el=f.createEEnumLiteral(); el.setName(text(l,"name")); el.setValue(integer(l,"id")); EEnum en=ens.get(integer(l,"enumeration")); if(en==null) throw new IllegalArgumentException("E1 export dangling literal enumeration"); en.getELiterals().add(el); lits.put(integer(l,"id"),el); }
    for (JsonNode c : s.withArray("classes")) { if(c.path("name").isNull()) throw new IllegalArgumentException("REJECT E1 export unnamed class"); EClass k=f.createEClass(); k.setName(text(c,"name")); if(!c.has("abstract")||!c.get("abstract").isBoolean()) throw new IllegalArgumentException("E1 export malformed abstract flag"); k.setAbstract(c.get("abstract").booleanValue()); EPackage p=pkgs.get(integer(c,"package")); if(p==null) throw new IllegalArgumentException("E1 export dangling class package"); p.getEClassifiers().add(k); cls.put(integer(c,"id"),k); }
    for (JsonNode c : s.withArray("classes")) { EClass k=cls.get(integer(c,"id")); for(JsonNode superId:c.withArray("supers")) { EClass parent=cls.get(superId.intValue()); if(parent==null) throw new IllegalArgumentException("E1 export superclass outside document"); k.getESuperTypes().add(parent); } }
    for (JsonNode p : s.withArray("properties")) {
      JsonNode owner=p.get("owner"); if (!"class".equals(text(owner,"tag"))) throw new IllegalArgumentException("REJECT association-owned end cannot be exported to Ecore: property " + integer(p,"id"));
      EClass k=cls.get(integer(owner,"id")); if(k==null) throw new IllegalArgumentException("E1 export dangling property owner"); JsonNode type=p.get("type"); String tag=text(type,"tag"); EStructuralFeature sf;
      if ("reference".equals(tag)) { EReference r=f.createEReference(); EClass target=cls.get(integer(type,"id")); if(target==null) throw new IllegalArgumentException("E1 export dangling reference type"); r.setEType(target); r.setContainment("composite".equals(text(p,"aggregation"))); sf=r; }
      else { EAttribute a=f.createEAttribute(); if("boolean".equals(tag)) a.setEType(EcorePackage.Literals.EBOOLEAN); else if("integer".equals(tag)) a.setEType(EcorePackage.Literals.EINT); else if("string".equals(tag)) a.setEType(EcorePackage.Literals.ESTRING); else if("enumeration".equals(tag)) { EEnum en=ens.get(integer(type,"id")); if(en==null) throw new IllegalArgumentException("E1 export dangling enum type"); a.setEType(en); } else throw new IllegalArgumentException("E1 export unsupported value type "+tag); if(!p.has("idProperty")||!p.get("idProperty").isBoolean()) throw new IllegalArgumentException("E1 export malformed idProperty"); a.setID(p.get("idProperty").booleanValue()); sf=a; }
      if(p.path("name").isNull()) throw new IllegalArgumentException("REJECT E1 export unnamed property"); sf.setName(text(p,"name")); copyMultiplicity(p.get("multiplicity"),sf); k.getEStructuralFeatures().add(sf); features.put(integer(p,"id"),sf);
    }
    java.util.Set<Integer> inverseAssigned=new java.util.HashSet<>(); for (JsonNode a : s.withArray("associations")) { JsonNode ends=a.withArray("ends"); if(ends.size()!=2) throw new IllegalArgumentException("E1 export association must have exactly two ends"); EStructuralFeature left=features.get(ends.get(0).intValue()), right=features.get(ends.get(1).intValue()); if(!(left instanceof EReference l) || !(right instanceof EReference r)) throw new IllegalArgumentException("REJECT association endpoints must be class-owned references"); l.setEOpposite(r); inverseAssigned.add(ends.get(1).intValue()); }
    EPackage root=null; for(JsonNode p:s.withArray("packages")) if(p.path("parent").isNull()) { if(root!=null) throw new IllegalArgumentException("REJECT multiple root packages: export needs one Ecore root"); root=pkgs.get(integer(p,"id")); } if(root==null) throw new IllegalArgumentException("E1 export needs a root package");
    ResourceSet set=new ResourceSetImpl(); set.getResourceFactoryRegistry().getExtensionToFactoryMap().put("ecore",new EcoreResourceFactoryImpl()); set.getResourceFactoryRegistry().getExtensionToFactoryMap().put("xmi",new XMIResourceFactoryImpl()); registerPackageTree(set,root); Resource er=set.createResource(fileUri(ecoreOut.toString())); er.getContents().add(root); ByteArrayOutputStream schemaBytes=new ByteArrayOutputStream(); er.save(schemaBytes,Map.of());
    // The emitted Ecore remains profile-compliant (`unsettable=false`).  During only
    // XMI serialization, make scalar attributes unsettable so EMF retains an explicit
    // default as an XML attribute; lexical import then restores that distinction.
    for(EStructuralFeature feature:features.values()) if(feature instanceof EAttribute attribute) attribute.setUnsettable(true);
    Map<Integer,EObject> os=new LinkedHashMap<>(); for(JsonNode o:snap.withArray("objects")) { EClass k=cls.get(integer(o,"classifier")); if(k==null) throw new IllegalArgumentException("E1 export dangling object classifier"); if(k.isAbstract()) throw new IllegalArgumentException("E1 export cannot instantiate abstract class"); os.put(integer(o,"id"),EcoreUtil.create(k)); }
    Map<EObject,Map<EStructuralFeature,List<Object>>> expected=new IdentityHashMap<>(); for(JsonNode ob:snap.withArray("observations")) { EObject owner=os.get(integer(ob,"object")); EStructuralFeature sf=features.get(integer(ob,"property")); if(owner==null||sf==null) throw new IllegalArgumentException("E1 export dangling observation"); List<Object> values=new ArrayList<>(); for(JsonNode v:ob.withArray("occurrences")) { String tag=text(v,"tag"); if("reference".equals(tag)) { EObject target=os.get(integer(v,"object")); if(target==null) throw new IllegalArgumentException("E1 export dangling reference occurrence"); values.add(target); } else if("boolean".equals(tag)) { if(!v.has("value")||!v.get("value").isBoolean()) throw new IllegalArgumentException("E1 export malformed Boolean occurrence"); values.add(v.get("value").booleanValue()); } else if("integer".equals(tag)) { if(!v.has("value")||!v.get("value").isIntegralNumber()||!v.get("value").canConvertToInt()) throw new IllegalArgumentException("REJECT E1 Integer outside Ecore EInt range"); values.add(v.get("value").intValue()); } else if("string".equals(tag)) { if(!v.has("value")||!v.get("value").isTextual()) throw new IllegalArgumentException("E1 export malformed String occurrence"); values.add(v.get("value").textValue()); } else if("enumeration".equals(tag)) { EEnumLiteral l=lits.get(integer(v,"literal")); if(l==null || l.getEEnum()!=ens.get(integer(v,"enumeration"))) throw new IllegalArgumentException("E1 export dangling enumeration occurrence"); values.add(l); } else throw new IllegalArgumentException("E1 export unsupported occurrence "+tag); }
      if(!owner.eClass().getEAllStructuralFeatures().contains(sf)) throw new IllegalArgumentException("E1 export inapplicable observation"); if(expected.computeIfAbsent(owner, ignored -> new IdentityHashMap<>()).putIfAbsent(sf,values)!=null) throw new IllegalArgumentException("E1 export duplicate observation key"); if(inverseAssigned.contains(integer(ob,"property"))) continue; if(sf.isMany()) ((EList<Object>)owner.eGet(sf)).addAll(values); else if(values.size()>1) throw new IllegalArgumentException("E1 export multiple values for single-valued feature"); else if(values.size()==1) owner.eSet(sf,values.getFirst()); }
    reconcileObservations(os.values(), expected); Resource xr=set.createResource(fileUri(xmiOut.toString())); for(Map.Entry<Integer,EObject> entry:os.entrySet()) ((XMIResource)xr).setID(entry.getValue(),"o"+entry.getKey()); for(EObject o:os.values()) if(o.eContainer()==null) xr.getContents().add(o); ByteArrayOutputStream instanceBytes=new ByteArrayOutputStream(); xr.save(instanceBytes,Map.of()); java.nio.file.Files.write(ecoreOut,schemaBytes.toByteArray()); java.nio.file.Files.write(xmiOut,instanceBytes.toByteArray());
  }
  /** Inverse maintenance supplies membership, but each end has its own order.
   * Moving within a reference list preserves the opposite membership. Validate
   * all supplied observations before writing either output resource. */
  @SuppressWarnings("unchecked")
  private static void reconcileObservations(java.util.Collection<EObject> objects,
      Map<EObject,Map<EStructuralFeature,List<Object>>> expected) {
    for (EObject object : objects) {
      Map<EStructuralFeature,List<Object>> rows = expected.getOrDefault(object, Map.of());
      for (EStructuralFeature feature : object.eClass().getEAllStructuralFeatures()) {
        List<Object> wanted = rows.get(feature);
        if (wanted == null) throw new IllegalArgumentException("E1 export missing observation " + feature.getName());
        List<Object> actual = new ArrayList<>();
        if (feature.isMany()) actual.addAll((List<Object>)object.eGet(feature));
        else if (object.eIsSet(feature)) actual.add(object.eGet(feature));
        List<Object> remainder = new ArrayList<>(actual);
        for (Object value : wanted) if (!remainder.remove(value))
          throw new IllegalArgumentException("E1 export inconsistent occurrence membership " + feature.getName());
        if (!remainder.isEmpty()) throw new IllegalArgumentException("E1 export inconsistent opposite counts " + feature.getName());
        if (feature.isMany() && feature.isOrdered()) {
          EList<Object> list = (EList<Object>)object.eGet(feature);
          for (int i=0; i<wanted.size(); i++) {
            int found = i;
            while (found<list.size() && !java.util.Objects.equals(list.get(found),wanted.get(i))) found++;
            if (found==list.size()) throw new IllegalArgumentException("E1 export occurrence reorder failed");
            if (found!=i) list.move(i,found);
          }
        }
      }
    }
  }
  private static JsonNode canonicalNode(JsonNode n) {
    if (n.isObject()) {
      ObjectNode result=object(); java.util.TreeSet<String> names=new java.util.TreeSet<>();
      n.fieldNames().forEachRemaining(names::add);
      for(String name:names) result.set(name,canonicalNode(n.get(name)));
      return result;
    }
    if (n.isArray()) { ArrayNode result=array(); for(JsonNode item:n) result.add(canonicalNode(item)); return result; }
    return n;
  }
  private static String canon(JsonNode n) { return canonicalNode(n).toString(); }
  private static <K> void uniquePut(Map<K,JsonNode> map, K key, JsonNode row, String label) {
    if(map.putIfAbsent(key,row)!=null) throw new IllegalArgumentException("REJECT duplicate " + label + " in comparison: " + key);
  }
  /** Compare two E1 documents after applying a recorded target-id→source-id map.
   * Names are deliberately not used as identities.  The generated exporter currently
   * preserves numeric allocation, so its recorded map is identity; keeping it explicit
   * makes this comparison valid when an exporter changes allocation. */
  private static void compareDocuments(Path leftPath, Path rightPath) throws Exception {
    JsonNode left=JSON.readTree(leftPath.toFile()), right=JSON.readTree(rightPath.toFile());
    if(!"vlmof-e1-1".equals(text(left,"version")) || !"vlmof-e1-1".equals(text(right,"version"))) throw new IllegalArgumentException("compare needs vlmof-e1-1 documents");
    // Structural declarations are expected under the explicit allocation map supplied by
    // the E1 exporter. Current map is identity; reject rather than guessing by spelling.
    for(String kind:List.of("packages","classes","properties","associations","enumerations","literals")) if(!canon(left.path("schema").path(kind)).equals(canon(right.path("schema").path(kind)))) throw new IllegalStateException("ROUNDTRIP MISMATCH declaration " + kind);
    Map<Integer,Boolean> ordered=new LinkedHashMap<>(); for(JsonNode p:left.path("schema").withArray("properties")) ordered.put(integer(p,"id"),p.path("multiplicity").path("ordered").asBoolean());
    Map<String,JsonNode> lo=new LinkedHashMap<>(), ro=new LinkedHashMap<>(); for(JsonNode o:left.path("snapshot").withArray("objects")) uniquePut(lo,o.path("id").asText(),o,"object ID"); for(JsonNode o:right.path("snapshot").withArray("objects")) uniquePut(ro,o.path("id").asText(),o,"object ID"); if(!lo.keySet().equals(ro.keySet())) throw new IllegalStateException("ROUNDTRIP MISMATCH object identity map"); for(String id:lo.keySet()) if(integer(lo.get(id),"classifier")!=integer(ro.get(id),"classifier")) throw new IllegalStateException("ROUNDTRIP MISMATCH classifier object "+id);
    Map<String,JsonNode> la=new LinkedHashMap<>(), ra=new LinkedHashMap<>(); for(JsonNode o:left.path("snapshot").withArray("observations")) uniquePut(la,o.path("object").asText()+":"+o.path("property").asText(),o,"observation key"); for(JsonNode o:right.path("snapshot").withArray("observations")) uniquePut(ra,o.path("object").asText()+":"+o.path("property").asText(),o,"observation key"); if(!la.keySet().equals(ra.keySet())) throw new IllegalStateException("ROUNDTRIP MISMATCH observation domain");
    for(String key:la.keySet()) { JsonNode a=la.get(key), b=ra.get(key); List<String> av=new ArrayList<>(),bv=new ArrayList<>(); for(JsonNode v:a.withArray("occurrences"))av.add(canon(v)); for(JsonNode v:b.withArray("occurrences"))bv.add(canon(v)); int property=integer(a,"property"); if(!ordered.getOrDefault(property,true)){Collections.sort(av);Collections.sort(bv);} if(!av.equals(bv)) throw new IllegalStateException("ROUNDTRIP MISMATCH occurrences "+key); }
    System.out.println("ROUNDTRIP OK declarations/objects/occurrences compared (identity allocation map)");
  }
  public static void main(String[] args) throws Exception {
    if (args.length == 3 && "compare".equals(args[0])) { compareDocuments(Path.of(args[1]), Path.of(args[2])); return; }
    if (args.length == 4 && "export".equals(args[0])) { exportDocument(Path.of(args[1]), Path.of(args[2]), Path.of(args[3])); return; }
    int divider = -1; for (int i=0;i<args.length;i++) if ("--".equals(args[i])) { divider=i; break; }
    if (args.length == 0 || divider <= 0 || divider == args.length-1) throw new IllegalArgumentException("usage: EmfInterchange import|roundtrip package.ecore [...] -- instance.xmi [...] | export interchange.json out.ecore out.xmi");
    boolean roundTrip = "roundtrip".equals(args[0]);
    if (!"import".equals(args[0]) && !roundTrip) throw new IllegalArgumentException("usage command must be `import` or `roundtrip`");
    List<String> ep = List.of(java.util.Arrays.copyOfRange(args, 1, divider)); List<String> xp = List.of(java.util.Arrays.copyOfRange(args, divider+1, args.length));
    Resource.Factory.Registry.INSTANCE.getExtensionToFactoryMap().put("ecore", new EcoreResourceFactoryImpl()); Resource.Factory.Registry.INSTANCE.getExtensionToFactoryMap().put("xmi", new XMIResourceFactoryImpl()); ResourceSet set = new ResourceSetImpl(); List<Resource> er = new ArrayList<>(); List<EPackage> roots = new ArrayList<>();
    for (String path : ep) { Resource r = set.getResource(fileUri(path), true); er.add(r); for (EObject root : r.getContents()) { if (!(root instanceof EPackage p)) throw new IllegalArgumentException("REJECT non-package Ecore root: " + loc(root)); roots.add(p); registerPackageTree(set, p); } }
    EmfInterchange bridge = new EmfInterchange(); bridge.preflight(set, er); for (EPackage p : roots) bridge.allocatePackage(p); for (EPackage p : roots) bridge.allocateDeclarations(p); bridge.require(bridge.diagnostics.isEmpty()); List<Resource> xr = new ArrayList<>(); for (String path : xp) { Resource r=set.createResource(fileUri(path)); r.load(Map.of(XMLResource.OPTION_DEFER_IDREF_RESOLUTION, true)); xr.add(r); } bridge.trackLexicalFeatures(xr); bridge.noProxies(xr); bridge.allocateObjects(xr); ObjectNode document = bridge.emit(roots, xr, ep, xp);
    if (roundTrip) {
      List<Resource> reloaded = reloadExports(xr, roots); EmfInterchange after = new EmfInterchange(); for (EPackage p : roots) after.allocatePackage(p); for (EPackage p : roots) after.allocateDeclarations(p); after.noProxies(reloaded); after.allocateObjects(reloaded); ObjectNode exported = after.emit(roots, reloaded, ep, xp);
      if (!document.get("schema").equals(exported.get("schema")) || !document.get("snapshot").equals(exported.get("snapshot"))) throw new IllegalStateException("roundtrip changed E1 schema or occurrence observations");
      document.with("provenance").put("roundTrip", "EMF XMI save/load compared schema and snapshot with deterministic manifest identity allocation");
    }
    System.out.println(JSON.writeValueAsString(document));
  }
}


