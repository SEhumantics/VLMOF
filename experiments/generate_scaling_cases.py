#!/usr/bin/env python3
"""Generate deterministic aligned scaling fixtures for the preregistered protocol."""

import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CASES = ROOT / "experiments" / "cases" / "emf-validation"


def write(path: Path, text: str) -> None:
    path.write_text(text, encoding="utf-8")


def manifest(path: Path, ident: str, ecore: str, xmi: str, family: str, counts: dict) -> None:
    data = {
        "id": ident,
        "condition": "dynamic-ecore-default-validator",
        "family": family,
        "ecore": [ecore], "xmi": [xmi],
        "obligation": "Accepted, losslessly aligned multi-size structural workload.",
        "state_relation": "EMF loaded observations must equal the E1 Core state under native identity correspondence.",
        "expected": {"emf": "accepted", "vlmof": "accepted"},
        "timing_eligible": True,
        "generator": {"script": "experiments/generate_scaling_cases.py", "version": 1, "parameters": counts},
    }
    write(path, json.dumps(data, indent=2) + "\n")


def tiny(output: Path, children: int) -> None:
    ident = f"containment-inheritance-{children + 1}"
    xmi = [
        '<?xml version="1.0" encoding="UTF-8"?>',
        '<tiny:Container xmlns:xmi="http://www.omg.org/XMI" xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"',
        '  xmlns:tiny="https://vlmof.example/evaluation/tiny" xmi:id="root"',
        '  xsi:schemaLocation="https://vlmof.example/evaluation/tiny tiny.ecore" name="root">',
    ]
    for i in range(children):
        xmi.append(f'  <children xsi:type="tiny:Child" xmi:id="c{i}" baseCode="B{i}" name="child-{i}" marks="{i} {i + 1}"/>')
    xmi.append('</tiny:Container>')
    write(output / f"{ident}.xmi", "\n".join(xmi) + "\n")
    manifest(output / f"{ident}.fixture.json", ident, "tiny.ecore", f"{ident}.xmi",
             "containment-inheritance", {"children": children, "objects": children + 1,
             "observations": 2 + children * 4, "occurrences": 1 + children * 6})


def train(output: Path, groups: int) -> None:
    ident = f"train-projection-{groups * 5}"
    lines = [
        '<?xml version="1.0" encoding="UTF-8"?>',
        '<xmi:XMI xmlns:xmi="http://www.omg.org/XMI" xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"',
        '  xmlns:railway="https://vlmof.example/evaluation/train-route-switch"',
        '  xsi:schemaLocation="https://vlmof.example/evaluation/train-route-switch train-route-switch.ecore">',
    ]
    for i in range(groups):
        r, sw, p, s1, s2 = (f"r{i}", f"sw{i}", f"p{i}", f"s{i}a", f"s{i}b")
        base = i * 10
        lines.append(f'  <railway:Route xmi:id="{r}" id="{base+1}" active="true" requires="{s1} {s2}"><follows xmi:id="{p}" id="{base+3}" position="STRAIGHT" route="{r}" target="{sw}"/></railway:Route>')
        lines.append(f'  <railway:Switch xmi:id="{sw}" id="{base+2}" currentPosition="STRAIGHT" positions="{p}"/>')
        lines.append(f'  <railway:Sensor xmi:id="{s1}" id="{base+4}"/><railway:Sensor xmi:id="{s2}" id="{base+5}"/>')
    lines.append('</xmi:XMI>')
    write(output / f"{ident}.xmi", "\n".join(lines) + "\n")
    manifest(output / f"{ident}.fixture.json", ident, "train-route-switch.ecore", f"{ident}.xmi",
             "train-projection", {"groups": groups, "objects": groups * 5,
             "observations": groups * 13, "occurrences": groups * 14})


def chain_schema(output: Path) -> None:
    write(output / "recursive-containment.ecore", '''<?xml version="1.0" encoding="UTF-8"?>
<ecore:EPackage xmi:version="2.0" xmlns:xmi="http://www.omg.org/XMI"
 xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance" xmlns:ecore="http://www.eclipse.org/emf/2002/Ecore"
 name="chain" nsURI="https://vlmof.example/evaluation/recursive-containment" nsPrefix="chain">
 <eClassifiers xsi:type="ecore:EClass" name="Node">
  <eStructuralFeatures xsi:type="ecore:EAttribute" name="name" lowerBound="1" eType="ecore:EDataType http://www.eclipse.org/emf/2002/Ecore#//EString"/>
  <eStructuralFeatures xsi:type="ecore:EReference" name="children" upperBound="-1" containment="true" eType="#//Node" eOpposite="#//Node/owner"/>
  <eStructuralFeatures xsi:type="ecore:EReference" name="owner" eType="#//Node" eOpposite="#//Node/children"/>
 </eClassifiers>
</ecore:EPackage>
''')


def chain(output: Path, objects: int) -> None:
    ident = f"recursive-containment-{objects}"
    lines = ['<?xml version="1.0" encoding="UTF-8"?>',
             '<chain:Node xmlns:xmi="http://www.omg.org/XMI" xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"',
             ' xmlns:chain="https://vlmof.example/evaluation/recursive-containment"',
             ' xsi:schemaLocation="https://vlmof.example/evaluation/recursive-containment recursive-containment.ecore" xmi:id="n0" name="node-0">']
    for i in range(1, objects):
        lines.append(' ' * i + f'<children xmi:id="n{i}" name="node-{i}">')
    for i in reversed(range(1, objects)):
        lines.append(' ' * i + '</children>')
    lines.append('</chain:Node>')
    write(output / f"{ident}.xmi", "\n".join(lines) + "\n")
    manifest(output / f"{ident}.fixture.json", ident, "recursive-containment.ecore", f"{ident}.xmi",
             "containment-inheritance", {"shape": "chain", "objects": objects,
             "observations": objects * 3, "occurrences": objects * 3 - 1,
             "maximum_containment_depth": objects - 1})


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=CASES)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    for children in (10, 100, 500): tiny(args.output, children)
    for groups in (2, 20, 100): train(args.output, groups)
    chain_schema(args.output)
    for objects in (11, 101, 501): chain(args.output, objects)


if __name__ == "__main__": main()
