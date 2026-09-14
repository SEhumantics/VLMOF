package org.vlmof.bridge;

import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.node.ArrayNode;
import com.fasterxml.jackson.databind.node.ObjectNode;
import java.util.*;

/** Explicit native-identity correspondence; never guesses identity from names. */
public final class IdentityCorrespondence {
  private static final String[] GROUPS={"packages","classes","properties","associations","enumerations","literals","objects"};
  private static int id(JsonNode n){if(!n.has("id")||!n.get("id").isIntegralNumber()||!n.get("id").canConvertToInt()||n.get("id").intValue()<0)throw new IllegalArgumentException("identity map row lacks integer id");return n.get("id").intValue();}
  private static String identity(JsonNode n){if(!n.has("identity")||!n.get("identity").isTextual())throw new IllegalArgumentException("identity map row lacks identity");return n.get("identity").textValue();}
  private static Map<Integer,Integer> mapping(String group, JsonNode sourceMap, JsonNode targetMap, JsonNode sourceItems, JsonNode targetItems){
    Map<String,Integer> sourceByNative=new HashMap<>(); Map<Integer,Integer> out=new HashMap<>(); Set<Integer> sourceIds=new HashSet<>(), targetIds=new HashSet<>();
    for(JsonNode r:sourceMap.path("identities").withArray(group)){int i=id(r);if(sourceByNative.putIfAbsent(identity(r),i)!=null)throw new IllegalArgumentException("duplicate source native identity "+group);if(!sourceIds.add(i))throw new IllegalArgumentException("duplicate source map ID "+group);}
    for(JsonNode r:targetMap.path("identities").withArray(group)){int t=id(r);Integer s=sourceByNative.get(identity(r));if(s==null||out.putIfAbsent(t,s)!=null)throw new IllegalArgumentException("missing or duplicate target native identity "+group);if(!targetIds.add(t))throw new IllegalArgumentException("duplicate target map ID "+group);}
    Set<Integer> actualS=new HashSet<>(),actualT=new HashSet<>();for(JsonNode x:sourceItems)if(!actualS.add(id(x)))throw new IllegalArgumentException("duplicate source declaration ID "+group);for(JsonNode x:targetItems)if(!actualT.add(id(x)))throw new IllegalArgumentException("duplicate target declaration ID "+group);
    if(!sourceIds.equals(actualS)||!targetIds.equals(actualT)||out.size()!=actualT.size()||out.size()!=actualS.size()||!new HashSet<>(out.values()).equals(actualS))throw new IllegalArgumentException("identity coverage failure "+group); return out;
  }
  private static int remap(Map<Integer,Integer> m,int x,String what){Integer y=m.get(x);if(y==null)throw new IllegalArgumentException("unmapped "+what+" id "+x);return y;}
  private static void set(ObjectNode n,String f,Map<Integer,Integer> m,String what){n.put(f,remap(m,n.get(f).intValue(),what));}
  /** Returns reimported deep copy normalized into source Core identifiers and list order. */
  public static JsonNode normalize(JsonNode source,JsonNode reimported,JsonNode map){
    if(!"vlmof-e1-map-1".equals(map.path("version").asText()))throw new IllegalArgumentException("unsupported identity map version"); JsonNode targetMap=reimported.path("provenance"); if(!targetMap.has("identities"))throw new IllegalArgumentException("reimported provenance lacks identities"); ObjectNode r=(ObjectNode)reimported.deepCopy(); Map<String,Map<Integer,Integer>> m=new HashMap<>();
    for(String g:GROUPS)m.put(g,mapping(g,map,targetMap,source.path(g.equals("objects")?"snapshot":"schema").path(g),r.path(g.equals("objects")?"snapshot":"schema").path(g)));
    ObjectNode s=(ObjectNode)r.path("schema"); for(JsonNode x:s.withArray("packages")){ObjectNode o=(ObjectNode)x;set(o,"id",m.get("packages"),"package");if(o.hasNonNull("parent"))set(o,"parent",m.get("packages"),"package");}
    for(JsonNode x:s.withArray("classes")){ObjectNode o=(ObjectNode)x;set(o,"id",m.get("classes"),"class");set(o,"package",m.get("packages"),"package");ArrayNode a=(ArrayNode)o.get("supers");for(int i=0;i<a.size();i++)a.set(i,com.fasterxml.jackson.databind.node.IntNode.valueOf(remap(m.get("classes"),a.get(i).intValue(),"class")));}
    for(JsonNode x:s.withArray("properties")){ObjectNode o=(ObjectNode)x;set(o,"id",m.get("properties"),"property");ObjectNode owner=(ObjectNode)o.get("owner");set(owner,"id",m.get("class".equals(owner.path("tag").asText())?"classes":"associations"),"owner");ObjectNode t=(ObjectNode)o.get("type");if(t.has("id"))set(t,"id",m.get("reference".equals(t.path("tag").asText())?"classes":"enumerations"),"type");}
    for(JsonNode x:s.withArray("associations")){ObjectNode o=(ObjectNode)x;set(o,"id",m.get("associations"),"association");set(o,"package",m.get("packages"),"package");ArrayNode a=(ArrayNode)o.get("ends");for(int i=0;i<2;i++)a.set(i,com.fasterxml.jackson.databind.node.IntNode.valueOf(remap(m.get("properties"),a.get(i).intValue(),"property")));}
    for(String g:new String[]{"enumerations","literals"})for(JsonNode x:s.withArray(g)){ObjectNode o=(ObjectNode)x;set(o,"id",m.get(g),g);if(g.equals("enumerations"))set(o,"package",m.get("packages"),"package");else set(o,"enumeration",m.get("enumerations"),"enumeration");}
    ObjectNode snap=(ObjectNode)r.path("snapshot");for(JsonNode x:snap.withArray("objects")){ObjectNode o=(ObjectNode)x;set(o,"id",m.get("objects"),"object");set(o,"classifier",m.get("classes"),"class");}for(JsonNode x:snap.withArray("observations")){ObjectNode o=(ObjectNode)x;set(o,"object",m.get("objects"),"object");set(o,"property",m.get("properties"),"property");for(JsonNode v:o.withArray("occurrences")){ObjectNode q=(ObjectNode)v;if("reference".equals(q.path("tag").asText()))set(q,"object",m.get("objects"),"object");if("enumeration".equals(q.path("tag").asText())){set(q,"enumeration",m.get("enumerations"),"enumeration");set(q,"literal",m.get("literals"),"literal");}}}
    for(String g:GROUPS){ArrayNode a=(ArrayNode)(g.equals("objects")?snap.get("objects"):s.get(g));Map<Integer,Integer> order=new HashMap<>();int i=0;for(JsonNode x:(g.equals("objects")?source.path("snapshot").withArray("objects"):source.path("schema").withArray(g)))order.put(id(x),i++);List<JsonNode> xs=new ArrayList<>();a.forEach(xs::add);xs.sort(Comparator.comparingInt(x->order.get(id(x))));a.removeAll();a.addAll(xs);} return r;
  }
}
