#!/usr/bin/env python3
"""Behavioral rejection tests for the EMF importer; no mock XML parser involved."""
import argparse, subprocess, tempfile
from pathlib import Path

parser=argparse.ArgumentParser(); parser.add_argument('--bridge',type=Path); parser.add_argument('--emf-compare',type=Path); args=parser.parse_args()
BRIDGE=args.bridge or Path(__file__).resolve().parents[1]
SAMPLES=Path(__file__).resolve().parents[1]/'src/main/resources/samples'
FIXTURE_BRIDGE=Path(__file__).resolve().parents[1]
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
with tempfile.TemporaryDirectory(prefix='e1-closure-') as d:
    d=Path(d)
    # Generate rather than hand-author: EMF writes a valid cross-resource
    # EType URI and a matching XMI instance for this actual load path.
    subprocess.run(['mvn','-q','exec:java',
                    '-Dexec.mainClass=org.vlmof.bridge.ExternalManifestFixture',
                    f'-Dexec.args={d}'], cwd=FIXTURE_BRIDGE, check=True)
    ext=d/'external.ecore'; main=d/'main.ecore'; xmi=d/'main.xmi'
    reject(main,xmi,'REJECT external classifier outside package manifest')
    p=subprocess.run(['mvn','-q','exec:java',f'-Dexec.mainClass={MAIN}',f'-Dexec.args=import {main} {ext} -- {xmi}'],cwd=BRIDGE,text=True,capture_output=True)
    assert p.returncode==0 and '"version":"vlmof-e1-1"' in p.stdout,p.stdout+p.stderr
    print('MANIFEST_OK explicit external Ecore closure emits interchange')
compare=args.emf_compare
if compare:
    p=subprocess.run(['mvn','-q','exec:java',f'-Dexec.mainClass={MAIN}',f'-Dexec.args=import {compare} -- {SAMPLES/"tiny.xmi"}'],cwd=BRIDGE,text=True,capture_output=True)
    text=p.stdout+p.stderr; assert p.returncode != 0 and 'REJECT operation' in text,text
    print('REJECT_OK EMFCompare operation')
else: print('NOT_RUN EMFCompare: pass --emf-compare /absolute/compare.ecore')
print('E1 IMPORT NEGATIVE REGRESSION OK')
