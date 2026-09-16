#!/usr/bin/env python3
"""Render the retained full Train Core state as explicit DSL; not a general importer.

Usage: python3 scripts/train_walkthrough.py CORE_JSON OUTPUT_DSL
The independent Lean experiment reparses/elaborates the output and requires exact
Schema and Snapshot equality, including declaration order and all empty rows.
"""
import json
import sys
from pathlib import Path


def render(d):
    s, m = d['schema'], d['snapshot']
    assert len(s['classes']) == 10 and len(s['properties']) == 21
    assert len(s['enumerations']) == 2 and len(s['associations']) == 3
    assert s['packages'] == [{'id': 0, 'name': 'railway', 'parent': None}]
    for store in ('classes', 'properties', 'associations', 'enumerations', 'literals'):
        assert [x['id'] for x in s[store]] == list(range(len(s[store])))
    assert [x['id'] for x in m['objects']] == list(range(len(m['objects'])))
    classes = {x['id']: 'railway::' + x['name'] for x in s['classes']}
    enums = {x['id']: 'railway::' + x['name'] for x in s['enumerations']}
    props = {x['id']: classes[x['owner']['id']] + '::' + x['name'] for x in s['properties']}
    lits = {x['id']: enums[x['enumeration']] + '::' + x['name'] for x in s['literals']}
    lines = ['package railway {']
    for e in s['enumerations']:
        lines += ['  enum ' + e['name'] + ' {']
        lines += ['    ' + l['name'] + ';' for l in s['literals'] if l['enumeration'] == e['id']]
        lines += ['  }']
    for c in s['classes']:
        supers = ' extends ' + ', '.join(classes[i] for i in c['supers']) if c['supers'] else ''
        lines += ['  ' + ('abstract ' if c['abstract'] else '') + 'class ' + c['name'] + supers + ' {']
        for p in s['properties']:
            assert p['owner']['tag'] == 'class'
            if p['owner']['id'] != c['id']:
                continue
            t, mult = p['type'], p['multiplicity']
            typ = {'boolean': 'Boolean', 'integer': 'Integer', 'string': 'String'}.get(t['tag'])
            if t['tag'] == 'reference': typ = classes[t['id']]
            if t['tag'] == 'enumeration': typ = 'enum ' + enums[t['id']]
            upper = str(mult['upper']['value']) if mult['upper']['tag'] == 'finite' else '*'
            flags = ('ordered' if mult['ordered'] else 'unordered') + ' ' + ('unique' if mult['unique'] else 'nonunique')
            if p['aggregation'] == 'composite': flags += ' composite'
            if p['idProperty']: flags += ' (id)'
            lines += [f"    {p['name']} : {typ} [{mult['lower']}..{upper}] {flags};"]
        lines += ['  }']
    for a in s['associations']:
        lines += [f"  association {a['name']} {{", '    ends ' + ', '.join(props[i] for i in a['ends']) + ';', '  }']
    lines += ['}', '']
    def value(v):
        if v['tag'] == 'reference': return '@o' + str(v['object'])
        if v['tag'] == 'enumeration': return lits[v['literal']]
        return json.dumps(v['value'], ensure_ascii=True)
    seen = []
    for o in m['objects']:
        lines += [f"object o{o['id']} : {classes[o['classifier']]} {{"]
        for a in m['observations']:
            if a['object'] != o['id']: continue
            seen.append(a)
            lines += ['  observe ' + props[a['property']] + ' = [' + ', '.join(value(v) for v in a['occurrences']) + '];']
        lines += ['}', '']
    assert seen == m['observations'], 'input row order cannot be retained by object-grouped DSL'
    return '\n'.join(lines)


if __name__ == '__main__':
    if len(sys.argv) != 3:
        raise SystemExit(__doc__)
    Path(sys.argv[2]).write_text(render(json.loads(Path(sys.argv[1]).read_text())), encoding='utf-8')
