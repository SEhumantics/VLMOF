#!/usr/bin/env python3
"""Regression: preserve lexical defaults and respect the native opposite boundary."""
import copy, json, subprocess, tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MAIN = "org.vlmof.bridge.EmfInterchange"

def many(): return {"lower": 0, "upper": {"tag": "unlimited"}, "ordered": True, "unique": False}
def one(): return {"lower": 0, "upper": {"tag": "finite", "value": 1}, "ordered": False, "unique": True}
def prop(i, name, typ, mult, aggregation="none"):
    return {"id": i, "name": name, "owner": {"tag":"class", "id":0}, "type":typ,
            "multiplicity":mult, "aggregation":aggregation, "idProperty":False}
def obs(obj, p, values): return {"object":obj,"property":p,"occurrences":values}
def value(tag, v=None):
    d={"tag":tag}
    if tag == "enumeration": d.update({"enumeration":0,"literal":0})
    elif tag == "reference": d["object"]=v
    else: d["value"]=v
    return d

doc = {"version":"vlmof-e1-1", "schema": {
  "packages":[{"id":0,"name":"regression","parent":None}],
  "classes":[{"id":0,"name":"A","package":0,"abstract":False,"supers":[]}],
  "properties":[
    prop(0,"flag",{"tag":"boolean"},one()), prop(1,"count",{"tag":"integer"},one()),
    prop(2,"label",{"tag":"string"},one()), prop(3,"state",{"tag":"enumeration","id":0},one()),
    prop(4,"children",{"tag":"reference","id":0},many(),"composite"),
    prop(5,"links",{"tag":"reference","id":0},many()), prop(6,"backLinks",{"tag":"reference","id":0},many()),
    prop(7,"scores",{"tag":"integer"},many())],
  "associations":[{"id":0,"name":"links__backLinks","package":0,"ends":[5,6]}],
  "enumerations":[{"id":0,"name":"State","package":0}],
  "literals":[{"id":0,"name":"FIRST","enumeration":0}]},
  "snapshot":{"objects":[{"id":0,"classifier":0},{"id":1,"classifier":0}],"observations":[
    obs(0,0,[value("boolean",False)]), obs(0,1,[value("integer",0)]),
    obs(0,2,[value("string","")]), obs(0,3,[value("enumeration")]),
    obs(0,4,[value("reference",1)]),obs(0,5,[value("reference",1)]), obs(0,6,[]),obs(0,7,[value("integer",0),value("integer",0)]),
    obs(1,0,[]),obs(1,1,[]),obs(1,2,[]),obs(1,3,[]),obs(1,4,[]),obs(1,5,[]),obs(1,6,[value("reference",0)]),obs(1,7,[])]},
  "provenance":{"test":"lexical-default-and-repeated-opposite-v1"}}

def run(args):
    subprocess.run(["mvn","-q","exec:java",f"-Dexec.mainClass={MAIN}",f"-Dexec.args={args}"], cwd=ROOT, check=True)

d=Path(tempfile.mkdtemp(prefix="e1-regression-")); source=d/"source.json"; ecore=d/"generated.ecore"; xmi=d/"generated.xmi"; reloaded=d/"reloaded.json"
source.write_text(json.dumps(doc))
run(f"export {source} {ecore} {xmi}")
with reloaded.open("w") as out:
    result=subprocess.run(["mvn","-q","exec:java",f"-Dexec.mainClass={MAIN}",f"-Dexec.args=import {ecore} -- {xmi}"],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
    if result.returncode: raise RuntimeError(result.stdout + result.stderr)
    out.write(result.stdout)
run(f"compare {source} {reloaded}")
got=json.loads(reloaded.read_text()); observations={(x["object"],x["property"]):x["occurrences"] for x in got["snapshot"]["observations"]}
assert observations[(0,0)] == [value("boolean",False)]
assert observations[(0,1)] == [value("integer",0)]
assert observations[(0,2)] == [value("string","")]
assert observations[(0,3)] == [value("enumeration")]
assert observations[(0,5)] == [value("reference",1)]
assert observations[(1,6)] == [value("reference",0)]
assert observations[(0,7)] == [value("integer",0),value("integer",0)]
bad=copy.deepcopy(doc); bad["snapshot"]["observations"][5]["occurrences"].append(value("reference",1))
badfile=d/"repeated-paired.json"; badfile.write_text(json.dumps(bad))
failed=subprocess.run(["mvn","-q","exec:java",f"-Dexec.mainClass={MAIN}",f"-Dexec.args=export {badfile} {d/'bad.ecore'} {d/'bad.xmi'}"],cwd=ROOT,capture_output=True,text=True)
assert failed.returncode != 0 and "UNSUPPORTED repeated paired reference occurrence" in failed.stdout + failed.stderr
assert not (d/'bad.ecore').exists() and not (d/'bad.xmi').exists()

# Opposite membership determines counts, but each ordered end has its own sequence.
ordered=copy.deepcopy(doc)
ordered['snapshot']['objects'].append({'id':2,'classifier':0})
for p in range(8): ordered['snapshot']['observations'].append(obs(2,p,[]))
bykey={(o['object'],o['property']):o for o in ordered['snapshot']['observations']}
bykey[(0,4)]['occurrences']=[value('reference',1),value('reference',2)]
bykey[(0,5)]['occurrences']=[value('reference',2)]
bykey[(1,5)]['occurrences']=[value('reference',2)]
bykey[(1,6)]['occurrences']=[]
bykey[(2,6)]['occurrences']=[value('reference',1),value('reference',0)]
orderedfile=d/'ordered.json'; orderedfile.write_text(json.dumps(ordered))
run(f'export {orderedfile} {d/"ordered.ecore"} {d/"ordered.xmi"}')
result=subprocess.run(['mvn','-q','exec:java',f'-Dexec.mainClass={MAIN}',
    f'-Dexec.args=import {d/"ordered.ecore"} -- {d/"ordered.xmi"}'],cwd=ROOT,capture_output=True,text=True)
assert result.returncode == 0, result.stdout+result.stderr
orderedreload=d/'ordered-reloaded.json'; orderedreload.write_text(result.stdout)
run(f'compare {orderedfile} {orderedreload}')

# Inconsistent inverse observations must not be repaired into a different snapshot.
bykey[(2,6)]['occurrences']=[value('reference',1)]
inconsistent=d/'inconsistent.json'; inconsistent.write_text(json.dumps(ordered))
failed=subprocess.run(['mvn','-q','exec:java',f'-Dexec.mainClass={MAIN}',
    f'-Dexec.args=export {inconsistent} {d/"inconsistent.ecore"} {d/"inconsistent.xmi"}'],cwd=ROOT,capture_output=True,text=True)
assert failed.returncode != 0 and 'inconsistent opposite counts' in failed.stdout+failed.stderr
assert not (d/'inconsistent.ecore').exists() and not (d/'inconsistent.xmi').exists()

# JSON member order is presentation; duplicate observation identities are not.
reformatted=d/'reformatted.json'; reformatted.write_text(json.dumps(doc,sort_keys=True))
run(f'compare {source} {reformatted}')
duplicates=copy.deepcopy(doc); duplicates['snapshot']['observations'].append(copy.deepcopy(duplicates['snapshot']['observations'][0]))
duplicatefile=d/'duplicate-key.json'; duplicatefile.write_text(json.dumps(duplicates))
failed=subprocess.run(['mvn','-q','exec:java',f'-Dexec.mainClass={MAIN}',
    f'-Dexec.args=compare {source} {duplicatefile}'],cwd=ROOT,capture_output=True,text=True)
assert failed.returncode != 0 and 'duplicate observation key' in failed.stdout+failed.stderr
print("E1 EXPORT REGRESSION OK explicit-defaults omitted-values repeated-scalars simple-opposites repeated-paired-unsupported")
