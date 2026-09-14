#!/usr/bin/env python3
"""Behavioral rejection tests for the EMF importer; no mock XML parser involved."""
import argparse, subprocess
from pathlib import Path

parser=argparse.ArgumentParser(); parser.add_argument('--bridge',type=Path); parser.add_argument('--emf-compare',type=Path); args=parser.parse_args()
BRIDGE=args.bridge or Path(__file__).resolve().parents[1]
SAMPLES=Path(__file__).resolve().parents[1]/'src/main/resources/samples'
MAIN='org.vlmof.bridge.EmfInterchange'
def reject(ecore,xmi,needle):
    p=subprocess.run(['mvn','-q','exec:java',f'-Dexec.mainClass={MAIN}',f'-Dexec.args=import {ecore} -- {xmi}'],cwd=BRIDGE,text=True,capture_output=True)
    text=p.stdout+p.stderr
    assert p.returncode != 0 and needle in text,(needle,text)
    print('REJECT_OK',needle)

reject(SAMPLES/'default-negative.ecore',SAMPLES/'tiny.xmi','REJECT default-value-literal')
reject(SAMPLES/'derived-custom-negative.ecore',SAMPLES/'tiny.xmi','REJECT derived-feature')
reject(SAMPLES/'custom-negative.ecore',SAMPLES/'tiny.xmi','REJECT custom-or-unsupported-datatype')
reject(SAMPLES/'generic-negative.ecore',SAMPLES/'tiny.xmi','REJECT generic-type')
reject(SAMPLES/'broken-reference.ecore',SAMPLES/'broken-reference.xmi','REJECT unresolved-proxy-reference')
compare=args.emf_compare
if compare:
    p=subprocess.run(['mvn','-q','exec:java',f'-Dexec.mainClass={MAIN}',f'-Dexec.args=import {compare} -- {SAMPLES/"tiny.xmi"}'],cwd=BRIDGE,text=True,capture_output=True)
    text=p.stdout+p.stderr; assert p.returncode != 0 and 'REJECT operation' in text,text
    print('REJECT_OK EMFCompare operation')
else: print('NOT_RUN EMFCompare: pass --emf-compare /absolute/compare.ecore')
print('E1 IMPORT NEGATIVE REGRESSION OK')
