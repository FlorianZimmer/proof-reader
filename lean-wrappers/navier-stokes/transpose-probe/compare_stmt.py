#!/usr/bin/env python3
"""Compare the #dump_statement_hashes records of the two probe environments.

Usage: compare_stmt.py READABLE_LOG LIBRARY_LOG > stmt-diff.json
Auxiliary proof constants (`foo._proof_N`) were already replaced, inside the
Lean probe, by a name made from the hash of their statement. Exit 0 when the
two statement closures agree constant by constant, 1 otherwise, 2 on bad input.
"""
import json
import sys
from pathlib import Path

FIELDS = ["kind", "levels", "type_hash", "type_len", "value_hash", "value_len", "hints"]


def read(path):
    rows = {}
    for line in Path(path).read_text(errors="replace").splitlines():
        line = line.strip()
        if line.startswith("{") and "stmt_name" in line:
            try:
                row = json.loads(line)
            except json.JSONDecodeError:
                continue
            rows.setdefault(row["stmt_name"], row)
    return rows


def main():
    left, right = read(sys.argv[1]), read(sys.argv[2])
    if not left or not right:
        print(json.dumps({"status": "incomplete", "readable": len(left), "library": len(right)}))
        return 2
    differing, only_readable, only_library = [], [], []
    for name in sorted(left.keys() | right.keys()):
        a, b = left.get(name), right.get(name)
        if a is None:
            only_library.append(name)
        elif b is None:
            only_readable.append(name)
        else:
            d = {k: [a.get(k), b.get(k)] for k in FIELDS if a.get(k) != b.get(k)}
            if d:
                differing.append({"name": name, "fields": d})
    report = {
        "status": "identical" if not (differing or only_readable or only_library) else "differing",
        "constants_compared": len(left.keys() & right.keys()),
        "readable_total": len(left), "library_total": len(right),
        "differing": differing, "only_in_readable": only_readable, "only_in_library": only_library,
    }
    print(json.dumps(report, indent=2))
    return 0 if report["status"] == "identical" else 1


if __name__ == "__main__":
    sys.exit(main())
