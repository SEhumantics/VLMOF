#!/usr/bin/env python3
"""Materialize only the audited Train enum omissions into a separate XMI copy.

The original is read-only.  The JSON manifest binds the input/output SHA-256 values
and every XPath-like containment path where `FAILURE` was inserted.
"""
import hashlib, json, sys
from pathlib import Path
from xml.etree import ElementTree as ET

XSI = "{http://www.w3.org/2001/XMLSchema-instance}type"

def digest(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def visit(node, path, changes):
    typ = node.attrib.get(XSI, "")
    # `follows` is SwitchPosition in this concrete Train serialization; switches
    # use an xsi:type because they share the `elements` containment feature.
    if node.tag.endswith("follows") and "position" not in node.attrib:
        node.set("position", "FAILURE"); changes.append({"path": path, "feature": "position", "value": "FAILURE"})
    if typ.endswith("Switch") and "currentPosition" not in node.attrib:
        node.set("currentPosition", "FAILURE"); changes.append({"path": path, "feature": "currentPosition", "value": "FAILURE"})
    counts = {}
    for child in node:
        local = child.tag.rsplit("}", 1)[-1]; n = counts.get(local, 0); counts[local] = n + 1
        visit(child, f"{path}/{local}[{n}]", changes)
def main():
    if len(sys.argv) != 4: raise SystemExit("usage: adapt_train_defaults.py ORIGINAL.xmi ADAPTED.xmi MANIFEST.json")
    source, output, manifest = map(Path, sys.argv[1:]); tree = ET.parse(source); changes=[]
    visit(tree.getroot(), "/RailwayContainer[0]", changes)
    if output.exists() or manifest.exists(): raise SystemExit("refusing to overwrite adaptation outputs")
    ET.register_namespace("xmi", "http://www.omg.org/XMI"); ET.register_namespace("xsi", "http://www.w3.org/2001/XMLSchema-instance"); ET.register_namespace("railway", "http://www.semanticweb.org/ontologies/2015/trainbenchmark")
    tree.write(output, encoding="ASCII", xml_declaration=True)
    manifest.write_text(json.dumps({"kind":"train-default-materialization-v1","original":str(source),"originalSha256":digest(source),"adapted":str(output),"adaptedSha256":digest(output),"insertions":changes}, indent=2)+"\n")
    print(f"ADAPTED insertions={len(changes)} original={digest(source)} adapted={digest(output)}")
if __name__ == "__main__": main()
