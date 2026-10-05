"""Check that every Lean identifier cited in main.tex exists in the tree.

Extracts identifiers from \\lean{...} and from lstlisting blocks (theorem/def names), takes the last dotted component,
and looks for a declaration `theorem|lemma|def|abbrev|structure|instance <name>` (optionally namespaced) under
RequestProject/, the vendored PNT+ package, or Mathlib. Identifiers that are not declarations (file paths, shell text,
axiom names, revision hashes, Lean keywords/tactics) are listed in SKIP.
Exit code 0 iff nothing is missing.
"""
import os
import re
import subprocess
import sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..'))
TEX = open(os.path.join(os.path.dirname(__file__), 'main.tex'), encoding='utf-8').read()

SKIP = {
    'propext', 'Classical.choice', 'Quot.sound', 'sorry', 'native_decide', 'Lean.ofReduceBool', 'norm_num',
    '#print axioms', 'v4.34.0', '21998bb', 'IEANTN/ZetaDefinitions.lean', 'tmp/att271_station_emitter.py',
    'papers/rh_window/Check.lean', 'papers/rh_window/ARTIFACT.md', '/usr/bin/time -l',
    '[propext, Classical.choice, Quot.sound]', 'station_301o2_sign', 'line t', 'laneChart3D σ y',
    'riemannZeta.RH_up_to (1269/2)', 'ZD.xiOrderNat z := analyticOrderNatAt riemannXi z',
    'completedRiemannZeta₀', 'stripZeroFinset T', 'IEANTN.ZetaDefinitions',
    'lean4checker', 'lake env lean -o', 'lake env lean', 'Check.lean', 'ARTIFACT.md', 'papers/rh_window/',
}

names = set(re.findall(r'\\lean\{([^}]*)\}', TEX))
for block in re.findall(r'\\begin\{lstlisting\}(.*?)\\end\{lstlisting\}', TEX, re.S):
    names |= set(re.findall(r'(?:theorem|def)\s+([A-Za-z_][\w.\']*)', block))

# expand a few compound cited forms to their declaration names
extra = {'station_301o2_sign', 'completedRiemannZeta₀', 'stripZeroFinset', 'analyticOrderNatAt', 'riemannXi',
         'laneChart3D', 'RiemannHypothesis', 'hardyG', 'theta', 'line'}
names |= extra

def found(last):
    if last == 'station_301o2_sign':
        return subprocess.run(['grep', '-qE', r'theorem station_301o2_sign\b',
                               os.path.join(ROOT, 'RequestProject/DVPStation301o2.lean')]).returncode == 0
    pat = r"(theorem|lemma|def|abbrev|structure|instance|noncomputable def)\s+([A-Za-z0-9_.']*\.)?" + re.escape(last) + r'\b'
    for d in ['RequestProject', '.lake/packages/PrimeNumberTheoremAnd', '.lake/packages/mathlib/Mathlib']:
        r = subprocess.run(['grep', '-rqE', '--include=*.lean', '--exclude=DVPStation[0-9]*.lean', pat, os.path.join(ROOT, d)])
        if r.returncode == 0:
            return True
    return False

missing = []
checked = 0
for n in sorted(names):
    if n in SKIP and n not in extra:
        continue
    last = n.split('.')[-1] if not n.startswith('RHBridge') else n.split('.')[-1]
    last = last.strip()
    if not re.fullmatch(r"[\w'₀]+", last):
        continue
    checked += 1
    if not found(last):
        missing.append(n)

print('identifiers checked:', checked)
print('missing:', len(missing))
for m in missing:
    print('  MISSING', m)
sys.exit(1 if missing else 0)
