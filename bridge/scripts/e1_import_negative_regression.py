#!/usr/bin/env python3
"""Behavioral rejection tests for the EMF importer; no mock XML parser involved."""
import subprocess
from pathlib import Path

BRIDGE=Path('/home/xoruser/msc-5/repo/Lean4MDE/workers/bridge-review/bridge')
SAMPLES=Path('/home/xoruser/msc-5/repo/Lean4MDE/workers/e1-bridge/bridge/src/main/resources/samples')
MAIN='org.vlmof.bridge.EmfInterchange'
def reject(ecore,xmi,needle):
    p=subprocess.run(['mvn','-q','exec:java',f'-Dexec.mainClass={MAIN}',f'-Dexec.args=import {ecore} -- {xmi}'],cwd=BRIDGE,text=True,capture_output=True)
    text=p.stdout+p.stderr
    assert p.returncode != 0 and needle in text,(needle,text)
    print('REJECT_OK',needle)

reject(SAMPLES/'default-negative.ecore',SAMPLES/'tiny.xmi','REJECT default-value-literal')
reject(SAMPLES/'derived-custom-negative.ecore',SAMPLES/'tiny.xmi','REJECT derived-feature')
reject(SAMPLES/'generic-negative.ecore',SAMPLES/'tiny.xmi','REJECT generic-type')
reject(SAMPLES/'broken-reference.ecore',SAMPLES/'broken-reference.xmi','REJECT unresolved-proxy-reference')
compare=Path('/tmp/public-cases/emf-compare/plugins/org.eclipse.emf.compare/model/compare.ecore')
if compare.exists():
    p=subprocess.run(['mvn','-q','exec:java',f'-Dexec.mainClass={MAIN}',f'-Dexec.args=import {compare} -- {SAMPLES/"tiny.xmi"}'],cwd=BRIDGE,text=True,capture_output=True)
    text=p.stdout+p.stderr; assert p.returncode != 0 and 'REJECT operation' in text,text
    print('REJECT_OK EMFCompare operation')
print('E1 IMPORT NEGATIVE REGRESSION OK')
