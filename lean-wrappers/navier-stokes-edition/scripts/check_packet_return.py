#!/usr/bin/env python3
"""Check a Lean statement-layer return against its packet.

    python3 tools/check_return.py RETURN_DIR [--packet PACKET_DIR]

Checks: no sorry, admit or new axiom; every theorem has a docstring; every numbered result of the
edition has a row in statements.json naming a declaration that the Lean files define, with a valid
status; open targets are definitions in OpenTargets.lean; every cited authors' declaration exists;
comparator.json permits only the three standard axioms. Compilation happens on public Actions.
"""
import json, re, sys
from pathlib import Path
args = sys.argv[1:]
ret = Path(args[0])
packet = Path(args[args.index('--packet') + 1]) if '--packet' in args else Path(__file__).resolve().parent.parent
problems = []
results = json.loads((packet / 'edition/numbered_results.json').read_text())
names = set(json.loads((packet / 'inputs/names.json').read_text()))
L = {p.name: p.read_text() for p in (ret / 'lean').rglob('*.lean')} if (ret / 'lean').is_dir() else {}
if 'EditionStatements.lean' not in L: problems.append('missing lean/EditionStatements.lean')
if 'OpenTargets.lean' not in L: problems.append('missing lean/OpenTargets.lean')
defined = {}
for fn, t in L.items():
    body = re.sub(r'/-.*?-/', lambda m: m.group(0) if m.group(0).startswith('/--') else ' ', t, flags=re.S)
    body = re.sub(r'--[^\n]*', '', body)
    if re.search(r'\bsorry\b|\badmit\b', body): problems.append(f'{fn}: contains sorry or admit')
    if re.search(r'^\s*axiom\s', body, re.M): problems.append(f'{fn}: declares an axiom')
    ns = re.findall(r'^\s*namespace\s+(\S+)', t, re.M)
    for m in re.finditer(r'(/--(?:(?!-/).)*-/\s*)?(?:@\[[^\]]*\]\s*)?(theorem|lemma|def|abbrev)\s+([^\s:({\[]+)', t, re.S):
        nm = m.group(3); defined[nm] = (fn, m.group(2))
        for n in ns: defined[f'{n}.{nm}'] = (fn, m.group(2))
        if m.group(2) in ('theorem', 'lemma') and not m.group(1): problems.append(f'{fn}: {nm} has no docstring')
try: S = json.loads((ret / 'statements.json').read_text())
except Exception as e: problems.append(f'statements.json: {e}'); S = {}
for r in results:
    if r['label'] not in S: problems.append(f'statements.json: no row for {r["label"]}')
for lab, v in S.items():
    if v.get('status') not in ('proved', 'reduced', 'open'): problems.append(f'{lab}: status {v.get("status")!r}')
    nm = v.get('lean', '')
    hit = defined.get(nm) or defined.get(nm.split('.')[-1])
    if not hit: problems.append(f'{lab}: {nm} is not defined in the returned files')
    elif v.get('status') == 'open' and hit[0] != 'OpenTargets.lean': problems.append(f'{lab}: open target {nm} must be in OpenTargets.lean')
    elif v.get('status') != 'open' and hit[1] not in ('theorem', 'lemma'): problems.append(f'{lab}: {nm} is {hit[1]}, expected a theorem')
    for u in v.get('uses', []):
        if u not in names: problems.append(f'{lab}: uses unknown declaration {u}')
    if not str(v.get('note', '')).strip(): problems.append(f'{lab}: no note')
try:
    cfg = json.loads((ret / 'comparator.json').read_text())
    ax = set(cfg.get('permitted_axioms', cfg.get('axioms', [])))
    if ax - {'propext', 'Quot.sound', 'Classical.choice'}: problems.append(f'comparator.json: extra axioms {sorted(ax - {"propext", "Quot.sound", "Classical.choice"})}')
except Exception as e: problems.append(f'comparator.json: {e}')
if not (ret / 'RETURN.md').is_file(): problems.append('missing RETURN.md')
if not (ret / 'README.md').is_file(): problems.append('missing README.md (the map from the layer to the paper)')
try:
    ctl = json.loads((ret / 'comparator-control.json').read_text())
    if not ctl.get('theorem_names'): problems.append('comparator-control.json: names no theorem')
except Exception as e: problems.append(f'comparator-control.json: {e}')
from collections import Counter
summary = {'numbered_results': len(results), 'rows': len(S), 'by_status': dict(Counter(v.get('status') for v in S.values())), 'lean_files': sorted(L)}
print(json.dumps({'summary': summary, 'problem_count': len(problems), 'problems': problems[:200]}, ensure_ascii=False, indent=1))
sys.exit(1 if problems else 0)
