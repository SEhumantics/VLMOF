package org.vlmof.bridge;

import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.databind.node.ArrayNode;
import com.fasterxml.jackson.databind.node.ObjectNode;
import java.nio.file.Path;
import java.security.MessageDigest;
import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import org.eclipse.emf.common.util.EList;
import org.eclipse.emf.common.util.TreeIterator;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.EAttribute;
import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.EClassifier;
import org.eclipse.emf.ecore.EDataType;
import org.eclipse.emf.ecore.EEnum;
import org.eclipse.emf.ecore.EEnumLiteral;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.EOperation;
import org.eclipse.emf.ecore.EPackage;
import org.eclipse.emf.ecore.EReference;
import org.eclipse.emf.ecore.EStructuralFeature;
import org.eclipse.emf.ecore.ETypeParameter;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.ResourceSet;
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl;
import org.eclipse.emf.ecore.util.EcoreUtil;
import org.eclipse.emf.ecore.xmi.impl.EcoreResourceFactoryImpl;
import org.eclipse.emf.ecore.xmi.impl.XMIResourceFactoryImpl;

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

  private void preflight(ResourceSet set, List<Resource> ecores) {
    for (Resource r : ecores) {
      for (EObject root : r.getContents()) inspect(root);
      TreeIterator<EObject> it = r.getAllContents(); while (it.hasNext()) inspect(it.next());
    }
    require(diagnostics.isEmpty());
  }
  private void inspect(EObject item) {
    if (item instanceof EOperation) reject("operation", item);
    if (item instanceof ETypeParameter) reject("generic-type-parameter", item);
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
  private void allocateObjectTree(EObject o) { if (objects.putIfAbsent(o, nextObject++) == null) for (EObject c : o.eContents()) allocateObjectTree(c); }

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
    for (Resource r : xmis) for (EObject root : r.getContents()) { if (root.eIsProxy()) reject("unresolved-proxy", root); TreeIterator<EObject> it = root.eAllContents(); while (it.hasNext()) { EObject o = it.next(); if (o.eIsProxy()) reject("unresolved-proxy", o); for (EReference ref : o.eClass().getEAllReferences()) { Object v = o.eGet(ref, false); if (v instanceof EObject e && e.eIsProxy()) reject("unresolved-proxy-reference", o); if (v instanceof List<?> xs) for (Object x : xs) if (x instanceof EObject e && e.eIsProxy()) reject("unresolved-proxy-reference", o); } } }
    require(diagnostics.isEmpty());
  }
  private ObjectNode emit(List<EPackage> roots, List<Resource> xmis, List<String> ecorePaths, List<String> xmiPaths) {
    ObjectNode out = object(); out.put("version", "vlmof-e1-1"); ObjectNode schema = object(); ArrayNode ps = array(), cs = array(), fs = array(), as = array(), es = array(), ls = array();
    for (EPackage p : roots) emitPackage(p, ps, cs, fs, as, es, ls); schema.set("packages", ps); schema.set("classes", cs); schema.set("properties", fs); schema.set("associations", as); schema.set("enumerations", es); schema.set("literals", ls); out.set("schema", schema);
    ObjectNode snapshot = object(); ArrayNode os = array(), observations = array();
    for (Map.Entry<EObject,Integer> entry : objects.entrySet()) { EObject o = entry.getKey(); ObjectNode on = object(); on.put("id", entry.getValue()); on.put("classifier", classes.get(o.eClass())); os.add(on); for (EStructuralFeature f : o.eClass().getEAllStructuralFeatures()) { if (!properties.containsKey(f)) continue; ObjectNode ob = object(); ob.put("object", entry.getValue()); ob.put("property", properties.get(f)); ArrayNode occ = array(); Object raw = o.eGet(f, false); if (raw instanceof List<?> values) for (Object v : values) occ.add(value(v, f)); else if (raw != null) occ.add(value(raw, f)); ob.set("occurrences", occ); observations.add(ob); } }
    snapshot.set("objects", os); snapshot.set("observations", observations); out.set("snapshot", snapshot);
    ObjectNode provenance = object(); provenance.put("allocation", "manifest-order package containment; manifest-order XMI containment preorder"); provenance.put("associationOwnership", "Ecore references are class-owned; paired references are exported as associations with class-owned ends"); ArrayNode pm = array(); for (String p : ecorePaths) pm.add(p); provenance.set("ecoreManifest", pm); ArrayNode im = array(); for (String p : xmiPaths) im.add(p); provenance.set("xmiManifest", im); out.set("provenance", provenance); return out;
  }
  private void emitPackage(EPackage p, ArrayNode ps, ArrayNode cs, ArrayNode fs, ArrayNode as, ArrayNode es, ArrayNode ls) {
    ObjectNode pn = object(); pn.put("id", packages.get(p)); named(pn, "name", p.getName()); idOrNull(pn, "parent", p.getESuperPackage() == null ? null : packages.get(p.getESuperPackage())); ps.add(pn);
    for (EClassifier c : p.getEClassifiers()) if (c instanceof EClass k && classes.containsKey(k)) { ObjectNode cn = object(); cn.put("id", classes.get(k)); named(cn, "name", k.getName()); cn.put("package", packages.get(p)); cn.put("abstract", k.isAbstract()); ArrayNode supers = array(); for (EClass s : k.getESuperTypes()) supers.add(classes.get(s)); cn.set("supers", supers); cs.add(cn); for (EStructuralFeature f : k.getEStructuralFeatures()) fs.add(property(f)); }
    for (EClassifier c : p.getEClassifiers()) if (c instanceof EEnum e) { ObjectNode en = object(); en.put("id", enums.get(e)); named(en, "name", e.getName()); en.put("package", packages.get(p)); es.add(en); for (EEnumLiteral l : e.getELiterals()) { ObjectNode ln = object(); ln.put("id", literals.get(l)); named(ln, "name", l.getName()); ln.put("enumeration", enums.get(e)); ls.add(ln); } }
    // A pair is emitted once, while both Ecore ends retain their actual class ownership.
    for (EClassifier c : p.getEClassifiers()) if (c instanceof EClass k) for (EReference r : k.getEReferences()) if (r.getEOpposite() != null && properties.get(r) < properties.get(r.getEOpposite())) { ObjectNode an = object(); an.put("id", as.size()); named(an, "name", r.getName() + "__" + r.getEOpposite().getName()); an.put("package", packages.get(p)); ArrayNode ends = array(); ends.add(properties.get(r)); ends.add(properties.get(r.getEOpposite())); an.set("ends", ends); as.add(an); }
    for (EPackage c : p.getESubpackages()) emitPackage(c, ps, cs, fs, as, es, ls);
  }
  public static void main(String[] args) throws Exception {
    int divider = -1; for (int i=0;i<args.length;i++) if ("--".equals(args[i])) { divider=i; break; }
    if (args.length == 0 || divider <= 0 || divider == args.length-1) throw new IllegalArgumentException("usage: EmfInterchange import package.ecore [...] -- instance.xmi [...]");
    if (!"import".equals(args[0])) throw new IllegalArgumentException("only `import` is supported; export requires a decoded Core document and is intentionally not inferred from XML");
    List<String> ep = List.of(java.util.Arrays.copyOfRange(args, 1, divider)); List<String> xp = List.of(java.util.Arrays.copyOfRange(args, divider+1, args.length));
    Resource.Factory.Registry.INSTANCE.getExtensionToFactoryMap().put("ecore", new EcoreResourceFactoryImpl()); Resource.Factory.Registry.INSTANCE.getExtensionToFactoryMap().put("xmi", new XMIResourceFactoryImpl()); ResourceSet set = new ResourceSetImpl(); List<Resource> er = new ArrayList<>(); List<EPackage> roots = new ArrayList<>();
    for (String path : ep) { Resource r = set.getResource(fileUri(path), true); er.add(r); for (EObject root : r.getContents()) { if (!(root instanceof EPackage p)) throw new IllegalArgumentException("REJECT non-package Ecore root: " + loc(root)); roots.add(p); set.getPackageRegistry().put(p.getNsURI(), p); } }
    EmfInterchange bridge = new EmfInterchange(); bridge.preflight(set, er); for (EPackage p : roots) bridge.allocatePackage(p); for (EPackage p : roots) bridge.allocateDeclarations(p); bridge.require(bridge.diagnostics.isEmpty()); List<Resource> xr = new ArrayList<>(); for (String path : xp) xr.add(set.getResource(fileUri(path), true)); bridge.noProxies(xr); bridge.allocateObjects(xr); System.out.println(JSON.writeValueAsString(bridge.emit(roots, xr, ep, xp)));
  }
}
