#!/usr/bin/env python3
"""Inventory the six pinned Train Benchmark XMI snapshots without EMF.

Usage: inventory_train_snapshots.py TRAIN_CHECKOUT OUTPUT_JSON
"""
import json
import pathlib
import sys
import xml.etree.ElementTree as ET

XSI_TYPE = "{http://www.w3.org/2001/XMLSchema-instance}type"
SNAPSHOTS = (
    "railway-batch-1.xmi",
    "railway-batch-2.xmi",
    "railway-inject-1.xmi",
    "railway-inject-2.xmi",
    "railway-repair-1.xmi",
    "railway-repair-2.xmi",
)
IMPLICIT_TYPES = {
    "routes": "Route",
    "follows": "SwitchPosition",
    "regions": "Region",
    "sensors": "Sensor",
    "semaphores": "Semaphore",
}
SCALARS = {
    "Region": ("id",),
    "Route": ("id", "active"),
    "Sensor": ("id",),
    "Switch": ("id", "currentPosition"),
    "Segment": ("id", "length"),
    "SwitchPosition": ("id", "position"),
    "Semaphore": ("id", "signal"),
}
REFERENCES = {
    "requires", "entry", "exit", "monitors", "monitoredBy", "connectsTo",
    "positions", "target",
}


def local_name(qname):
    return qname.rsplit("}", 1)[-1]


def element_type(element):
    source_type = element.get(XSI_TYPE)
    if source_type:
        return source_type.rsplit(":", 1)[-1]
    return IMPLICIT_TYPES.get(local_name(element.tag), local_name(element.tag))


def inventory(path):
    root = ET.parse(path).getroot()
    scalar = {}
    type_counts = {}
    ids = []
    reference_lists = 0
    repeated_target_lists = 0
    for element in root.iter():
        kind = element_type(element)
        type_counts[kind] = type_counts.get(kind, 0) + 1
        for field in SCALARS.get(kind, ()):
            record = scalar.setdefault(field, {"expected_instances": 0, "present": 0, "missing": 0})
            record["expected_instances"] += 1
            if field in element.attrib:
                record["present"] += 1
                if field == "id":
                    ids.append(element.attrib[field])
            else:
                record["missing"] += 1
        for name, value in element.attrib.items():
            if name in REFERENCES:
                reference_lists += 1
                targets = value.split()
                if len(targets) != len(set(targets)):
                    repeated_target_lists += 1
    return {
        "file": path.name,
        "objects_including_root": sum(type_counts.values()),
        "type_counts": dict(sorted(type_counts.items())),
        "scalar_fields": dict(sorted(scalar.items())),
        "ordinary_id_values": {"present": len(ids), "distinct": len(set(ids))},
        "serialized_reference_lists": reference_lists,
        "reference_lists_with_repeated_target_token": repeated_target_lists,
    }


def main():
    if len(sys.argv) != 3:
        raise SystemExit(f"usage: {sys.argv[0]} TRAIN_CHECKOUT OUTPUT_JSON")
    checkout = pathlib.Path(sys.argv[1])
    models = checkout / "models"
    records = [inventory(models / name) for name in SNAPSHOTS]
    output = {
        "source": "Train Benchmark v1.0 commit 6490047d7449f9a4b66cec032b9377bfc06a54d2",
        "method": "Python standard-library xml.etree.ElementTree; source inspection only, no EMF loading",
        "snapshots": records,
    }
    pathlib.Path(sys.argv[2]).write_text(json.dumps(output, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
