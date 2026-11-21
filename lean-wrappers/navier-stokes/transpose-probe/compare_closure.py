#!/usr/bin/env python3
"""Compare the #dump_closure records of the two probe environments.

Usage: compare_closure.py READABLE_LOG LIBRARY_LOG > diff.json
For every constant present on either side it reports which fields differ, and
for a differing string field the first differing position with context.
Exit 0 when every record is identical, 1 when some differ, 2 on missing input.
"""
import json
import sys
from pathlib import Path


def read(path):
    rows = {}
    for line in Path(path).read_text(errors="replace").splitlines():
        line = line.strip()
        if not line.startswith("{"):
            continue
        try:
            row = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(row, dict) and "closure_name" in row:
            rows.setdefault(row["closure_name"], row)
    return rows


def first_difference(a, b, width=160):
    n = min(len(a), len(b))
    i = next((k for k in range(n) if a[k] != b[k]), n)
    lo = max(0, i - width)
    return {"position": i, "readable_length": len(a), "library_length": len(b),
            "readable_context": a[lo:i + width], "library_context": b[lo:i + width]}


def main():
    if len(sys.argv) != 3:
        print(json.dumps({"status": "incomplete", "error": "two log paths needed"}))
        return 2
    left, right = read(sys.argv[1]), read(sys.argv[2])
    if not left or not right:
        print(json.dumps({"status": "incomplete", "readable_records": len(left),
                          "library_records": len(right)}))
        return 2
    report = []
    for name in sorted(left.keys() | right.keys()):
        a, b = left.get(name), right.get(name)
        if a is None or b is None:
            report.append({"name": name, "only_in": "library" if a is None else "readable"})
            continue
        diffs = {}
        for key in sorted(a.keys() | b.keys()):
            va, vb = a.get(key), b.get(key)
            if va == vb:
                continue
            if isinstance(va, str) and isinstance(vb, str):
                diffs[key] = first_difference(va, vb)
            else:
                diffs[key] = {"readable": va, "library": vb}
        report.append({"name": name, "identical": not diffs, "differences": diffs})
    same = all(r.get("identical") for r in report)
    print(json.dumps({"status": "identical" if same else "differing", "constants": report},
                     ensure_ascii=False, indent=2))
    return 0 if same else 1


if __name__ == "__main__":
    sys.exit(main())
