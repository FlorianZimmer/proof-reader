#!/usr/bin/env python3
"""Compare the JSON constant records emitted by the two separate Lean probes.
This is a diagnostic expression comparison, not a kernel check.
Usage: compare_probe_dumps.py READABLE_LOG LIBRARY_LOG
"""
from pathlib import Path
import json,re,sys
EXPECTED={'Breakdown.Space','Breakdown.unitVector','Breakdown.AdjointDefect.transposeApply'}
def read(path):
    text=Path(path).read_text()
    if re.search(r"(?m)(?:^|:\d+:\d+: )error:",text):
        raise ValueError(f'{path}: Lean error in probe log')
    rows={}
    for line in text.splitlines():
        try: row=json.loads(line)
        except json.JSONDecodeError: continue
        if isinstance(row,dict) and {'name','levels','type','value','constructors'}<=row.keys():
            if row['name'] in rows: raise ValueError(f'{path}: duplicate constant {row["name"]}')
            rows[row['name']]=row
    if not EXPECTED<=rows.keys(): raise ValueError(f'{path}: missing records: {sorted(EXPECTED-rows.keys())}')
    return rows
try:
    if len(sys.argv)!=3:raise ValueError('Supply exactly two probe log paths')
    left,right=map(read,sys.argv[1:])
except (ValueError,OSError) as e:
    print(json.dumps({'status':'incomplete','error':str(e)},indent=2));sys.exit(2)
rows=[]
for name in sorted(left.keys()|right.keys()):
    a,b=left.get(name),right.get(name)
    changes={}
    if a is None or b is None:changes['record']={'readable':a,'library':b}
    else:
        for k in a.keys()|b.keys():
            if a.get(k)!=b.get(k):changes[k]={'readable':a.get(k),'library':b.get(k)}
    rows.append({'name':name,'identical_normalized_record':not changes,'differences':changes})
identical=all(r['identical_normalized_record'] for r in rows)
print(json.dumps({'status':'identical_records' if identical else 'differing_records','evidence_limit':'Binder names and metadata were erased by DumpSupport. This comparison is not a proof of definitional or mathematical equivalence.','constants':rows},ensure_ascii=False,indent=2))
sys.exit(0 if identical else 1)
