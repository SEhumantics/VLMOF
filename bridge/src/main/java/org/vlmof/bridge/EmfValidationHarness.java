package org.vlmof.bridge;

import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.databind.node.ArrayNode;
import com.fasterxml.jackson.databind.node.ObjectNode;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.security.MessageDigest;
import java.util.ArrayList;
import java.util.HexFormat;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import org.eclipse.emf.common.util.BasicDiagnostic;
import org.eclipse.emf.common.util.Diagnostic;
import org.eclipse.emf.common.util.DiagnosticChain;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.EPackage;
import org.eclipse.emf.ecore.EValidator;
import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.EcorePackage;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.util.Diagnostician;
import org.eclipse.emf.ecore.util.EcoreUtil;
import org.eclipse.emf.ecore.util.EcoreValidator;
import org.eclipse.emf.ecore.util.EObjectValidator;
import org.eclipse.emf.ecore.impl.EValidatorRegistryImpl;
import org.eclipse.emf.ecore.xmi.impl.EcoreResourceFactoryImpl;
import org.eclipse.emf.ecore.xmi.impl.XMIResourceFactoryImpl;

/**
 * Actual EMF structural-validation entry point for a declared Ecore/XMI fixture.
 *
 * <p>This deliberately does not use {@link EmfInterchange}'s E1 profile checks.
 * It loads the declared resources into a fresh, manifest-closed resource set and
 * invokes a diagnostician with an isolated validator registry.  The standard
 * condition explicitly maps EcorePackage to EcoreValidator; dynamic packages
 * select EObjectValidator through EValidatorRegistryImpl's documented fallback.
 * Loader, validator, and timing observations are emitted separately as JSON.</p>
 */
public final class EmfValidationHarness {
  private static final ObjectMapper JSON = new ObjectMapper();

  private record Fixture(String id, Path manifest, List<Path> ecores, List<Path> xmis) {}
  private record Loaded(Fixture fixture, ClosedManifestResourceSet resources,
                        EValidatorRegistryImpl validators, Diagnostician diagnostician,
                        List<Resource> schemaResources, List<Resource> instanceResources) {}

  private static URI fileUri(Path path) {
    return URI.createFileURI(path.toAbsolutePath().normalize().toString());
  }

  private static String sha256(Path path) throws Exception {
    MessageDigest digest = MessageDigest.getInstance("SHA-256");
    try (InputStream input = Files.newInputStream(path)) {
      byte[] buffer = new byte[8192];
      for (int read; (read = input.read(buffer)) >= 0;) digest.update(buffer, 0, read);
    }
    return HexFormat.of().formatHex(digest.digest());
  }

  private static List<Path> paths(JsonNode node, String field, Path base) throws Exception {
    JsonNode values = node.get(field);
    if (values == null || !values.isArray() || values.isEmpty()) {
      throw new IllegalArgumentException("fixture field `" + field + "` must be a nonempty array");
    }
    List<Path> result = new ArrayList<>();
    for (JsonNode value : values) {
      if (!value.isTextual()) throw new IllegalArgumentException("fixture path must be text: " + field);
      Path path = base.resolve(value.textValue()).normalize().toAbsolutePath();
      if (!Files.isRegularFile(path)) throw new IllegalArgumentException("fixture file does not exist: " + path);
      result.add(path);
    }
    return result;
  }

  private static Fixture fixture(Path manifest) throws Exception {
    Path absolute = manifest.toAbsolutePath().normalize();
    JsonNode node = JSON.readTree(Files.readString(absolute));
    if (!node.isObject()) throw new IllegalArgumentException("fixture manifest must be a JSON object");
    JsonNode id = node.get("id");
    if (id == null || !id.isTextual() || id.textValue().isBlank()) {
      throw new IllegalArgumentException("fixture manifest needs nonempty `id`");
    }
    return new Fixture(id.textValue(), absolute, paths(node, "ecore", absolute.getParent()),
      paths(node, "xmi", absolute.getParent()));
  }

  private static void registerPackageTree(ClosedManifestResourceSet set, EPackage pkg) {
    set.getPackageRegistry().put(pkg.getNsURI(), pkg);
    for (EPackage child : pkg.getESubpackages()) registerPackageTree(set, child);
  }

  private static Loaded load(Fixture fixture) throws Exception {
    List<Path> manifest = new ArrayList<>(fixture.ecores());
    manifest.addAll(fixture.xmis());
    ClosedManifestResourceSet set = new ClosedManifestResourceSet(manifest);
    set.getResourceFactoryRegistry().getExtensionToFactoryMap().put("ecore", new EcoreResourceFactoryImpl());
    set.getResourceFactoryRegistry().getExtensionToFactoryMap().put("xmi", new XMIResourceFactoryImpl());
    List<Resource> schemas = new ArrayList<>();
    for (Path path : fixture.ecores()) {
      Resource resource = set.loadManifest(path);
      schemas.add(resource);
      for (EObject root : resource.getContents()) {
        if (!(root instanceof EPackage pkg)) throw new IllegalArgumentException("Ecore root is not EPackage: " + EcoreUtil.getURI(root));
        registerPackageTree(set, pkg);
      }
    }
    List<Resource> instances = new ArrayList<>();
    for (Path path : fixture.xmis()) instances.add(set.loadManifest(path));

    EValidatorRegistryImpl validators = new EValidatorRegistryImpl();
    // Force Ecore initialization before creating our isolated standard condition.
    EcorePackage.eINSTANCE.eClass();
    validators.put(EcorePackage.eINSTANCE, EcoreValidator.INSTANCE);
    return new Loaded(fixture, set, validators, new Diagnostician(validators), schemas, instances);
  }

  private static List<EObject> roots(List<Resource> resources) {
    List<EObject> result = new ArrayList<>();
    for (Resource resource : resources) result.addAll(resource.getContents());
    return result;
  }

  private static String uri(EObject object) {
    try { return EcoreUtil.getURI(object).toString(); }
    catch (RuntimeException ignored) { return "unavailable"; }
  }

  private static boolean containsError(Diagnostic diagnostic) {
    if (diagnostic.getSeverity() >= Diagnostic.ERROR) return true;
    for (Diagnostic child : diagnostic.getChildren()) if (containsError(child)) return true;
    return false;
  }

  private static void flatten(Diagnostic diagnostic, String rootUri, String validator, ArrayNode out) {
    ObjectNode row = out.addObject();
    row.put("root_uri", rootUri);
    row.put("validator", validator);
    row.put("severity", diagnostic.getSeverity());
    row.put("source", diagnostic.getSource());
    row.put("code", diagnostic.getCode());
    row.put("message", diagnostic.getMessage());
    ArrayNode data = row.putArray("data");
    if (diagnostic.getData() != null) for (Object value : diagnostic.getData()) {
      if (value instanceof EObject object) data.add(uri(object));
      else data.add(String.valueOf(value));
    }
    for (Diagnostic child : diagnostic.getChildren()) flatten(child, rootUri, validator, out);
  }

  /** Mirror Diagnostician's package/supertype/default-validator lookup for inventory. */
  private static EValidator effective(Loaded loaded, EObject root) {
    EClass type = root.eClass();
    Object selected;
    while ((selected = loaded.validators().get(type.eContainer())) == null) {
      if (type.getESuperTypes().isEmpty()) {
        selected = loaded.validators().get(null);
        break;
      }
      type = type.getESuperTypes().getFirst();
    }
    EValidator validator = (EValidator) selected;
    if (validator == null) throw new IllegalStateException("no validator for package " + root.eClass().getEPackage().getNsURI());
    return validator;
  }

  private static boolean validateRoots(Loaded loaded, List<EObject> roots, boolean diagnostics,
                                       String phase, ObjectNode output) {
    ArrayNode calls = output.putArray(phase + "_calls");
    ArrayNode problems = diagnostics ? output.withArray("diagnostics") : null;
    boolean accepted = true;
    for (EObject root : roots) {
      EValidator validator = effective(loaded, root);
      BasicDiagnostic chain = diagnostics ? new BasicDiagnostic() : null;
      boolean valid = loaded.diagnostician().validate(root, chain,
        loaded.diagnostician().createDefaultContext());
      boolean errors = chain != null && containsError(chain);
      ObjectNode call = calls.addObject();
      call.put("root_uri", uri(root));
      call.put("validator", validator.getClass().getName());
      call.put("returned", valid);
      call.put("has_error_diagnostic", errors);
      if (chain != null) flatten(chain, uri(root), validator.getClass().getName(), problems);
      accepted &= valid && !errors;
    }
    return accepted;
  }

  /** Boolean-only validation for the timed path: no diagnostic or JSON allocation. */
  private static boolean validateRootsBoolean(Loaded loaded, List<EObject> roots) {
    boolean accepted = true;
    for (EObject root : roots) {
      accepted &= loaded.diagnostician().validate(root, null,
        loaded.diagnostician().createDefaultContext());
    }
    return accepted;
  }

  private static ObjectNode registryInventory(Loaded loaded) {
    ObjectNode result = JSON.createObjectNode();
    ArrayNode entries = result.putArray("registry_entries");
    for (Map.Entry<EPackage, Object> entry : loaded.validators().entrySet()) {
      ObjectNode row = entries.addObject();
      row.put("package_ns_uri", entry.getKey() == null ? null : entry.getKey().getNsURI());
      row.put("stored_class", entry.getValue().getClass().getName());
      EValidator effective = loaded.validators().getEValidator(entry.getKey());
      row.put("effective_class", effective == null ? null : effective.getClass().getName());
    }
    LinkedHashMap<String, EObject> representatives = new LinkedHashMap<>();
    for (Resource resource : List.of(loaded.schemaResources(), loaded.instanceResources()).stream().flatMap(List::stream).toList()) {
      for (EObject root : resource.getContents()) {
        representatives.putIfAbsent(root.eClass().getEPackage().getNsURI(), root);
        var iterator = root.eAllContents();
        while (iterator.hasNext()) {
          EObject object = iterator.next();
          representatives.putIfAbsent(object.eClass().getEPackage().getNsURI(), object);
        }
      }
    }
    ArrayNode effective = result.putArray("effective_by_package");
    for (Map.Entry<String, EObject> entry : representatives.entrySet()) {
      ObjectNode row = effective.addObject();
      row.put("ns_uri", entry.getKey());
      row.put("validator", effective(loaded, entry.getValue()).getClass().getName());
    }
    result.putArray("validation_delegates");
    return result;
  }

  private static ObjectNode report(Loaded loaded, boolean diagnosticPass) {
    ObjectNode output = JSON.createObjectNode();
    output.put("format", "vlmof-emf-validation-1");
    output.put("fixture", loaded.fixture().id());
    ObjectNode inputs = output.putObject("inputs");
    try {
      for (Path path : loaded.fixture().ecores()) inputs.put(path.toString(), sha256(path));
      for (Path path : loaded.fixture().xmis()) inputs.put(path.toString(), sha256(path));
    } catch (Exception error) { throw new IllegalStateException("cannot hash fixture input", error); }
    output.set("validators", registryInventory(loaded));
    if (diagnosticPass) output.putArray("diagnostics");
    boolean schemas = validateRoots(loaded, roots(loaded.schemaResources()), diagnosticPass, "schema", output);
    boolean instances = validateRoots(loaded, roots(loaded.instanceResources()), diagnosticPass, "instance", output);
    output.put("schema_accepted", schemas);
    output.put("instance_accepted", instances);
    output.put("accepted", schemas && instances);
    return output;
  }

  private static ObjectNode warm(Loaded loaded, int warmups, int repetitions) {
    if (warmups < 0 || repetitions <= 0) throw new IllegalArgumentException("warmups >= 0 and repetitions > 0 required");
    ObjectNode output = report(loaded, true); // correctness/diagnostics are intentionally outside timing.
    ArrayNode samples = output.putArray("samples");
    List<EObject> all = new ArrayList<>(roots(loaded.schemaResources()));
    all.addAll(roots(loaded.instanceResources()));
    boolean allAccepted = true;
    for (int index = 0; index < warmups + repetitions; index++) {
      long start = System.nanoTime();
      boolean accepted = validateRootsBoolean(loaded, all);
      long elapsed = System.nanoTime() - start;
      ObjectNode sample = samples.addObject();
      sample.put("index", index);
      sample.put("warmup", index < warmups);
      sample.put("nanoseconds", elapsed);
      sample.put("accepted", accepted);
      allAccepted &= accepted;
    }
    output.put("timing_boundary", "preloaded-schema-and-instance-validation");
    output.put("all_timed_results_accepted", allAccepted);
    return output;
  }

  private static void usage() {
    System.err.println("usage: EmfValidationHarness validate MANIFEST.json | warm-validate MANIFEST.json WARMUPS REPETITIONS");
  }

  public static void main(String[] args) throws Exception {
    try {
      if (args.length < 2 || !("validate".equals(args[0]) || "warm-validate".equals(args[0]))) {
        usage(); System.exit(2); return;
      }
      Fixture fixture = fixture(Path.of(args[1]));
      Loaded loaded = load(fixture);
      ObjectNode result;
      if ("validate".equals(args[0])) {
        if (args.length != 2) { usage(); System.exit(2); return; }
        result = report(loaded, true);
      } else {
        if (args.length != 4) { usage(); System.exit(2); return; }
        result = warm(loaded, Integer.parseInt(args[2]), Integer.parseInt(args[3]));
      }
      System.out.println(JSON.writeValueAsString(result));
    } catch (Exception error) {
      ObjectNode result = JSON.createObjectNode();
      result.put("format", "vlmof-emf-validation-1");
      result.put("status", "execution-failure");
      result.put("error", error.toString());
      System.out.println(JSON.writeValueAsString(result));
      System.exit(1);
    }
  }
}
