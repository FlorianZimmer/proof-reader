#!/usr/bin/env python3
"""Check coverage, actual namespaces, proof holes, imports and comparison isolation.

These are source checks, not Lean elaboration or kernel checks.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import re
from collections import Counter
from pathlib import Path


def lean_code(text: str) -> str:
    """Remove nested comments and strings while retaining line positions."""
    out, i, depth, string = [], 0, 0, False
    while i < len(text):
        pair = text[i:i + 2]
        char = text[i]
        if depth:
            if pair == "/-": depth += 1; out.extend("  "); i += 2; continue
            if pair == "-/": depth -= 1; out.extend("  "); i += 2; continue
            out.append("\n" if char == "\n" else " "); i += 1; continue
        if string:
            if char == "\\" and i + 1 < len(text): out.extend("  "); i += 2; continue
            if char == '"': string = False
            out.append("\n" if char == "\n" else " "); i += 1; continue
        if pair == "/-": depth = 1; out.extend("  "); i += 2; continue
        if pair == "--":
            end = text.find("\n", i)
            if end < 0: out.extend(" " * (len(text) - i)); break
            out.extend(" " * (end - i)); i = end; continue
        if char == '"': string = True; out.append(" "); i += 1; continue
        out.append(char); i += 1
    if depth or string:
        raise ValueError("unterminated block comment or string")
    return "".join(out)


def declarations(code: str) -> dict[str, str]:
    stack: list[tuple[str, str]] = []
    result = {}
    for line in code.splitlines():
        head = re.match(r"\s*(?:noncomputable\s+)?(namespace|section)\b(?:\s+(\S+))?", line)
        if head:
            stack.append((head[1], head[2] or "")); continue
        if re.match(r"\s*end\b", line):
            if stack: stack.pop()
            continue
        match = re.match(r"\s*(?:(?:private|protected|noncomputable)\s+)*(theorem|lemma|def|abbrev|structure)\s+([^\s:({\[]+)", line)
        if match:
            prefix = ".".join(n for k, n in stack if k == "namespace")
            name = (prefix + "." if prefix else "") + match[2]
            if name.startswith("_root_."): name = name.removeprefix("_root_.")
            result[name] = match[1]
    return result


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("return_folder", nargs="?", type=Path, default=Path(__file__).resolve().parents[1])
    ap.add_argument("--packet", type=Path)
    args = ap.parse_args()
    root = args.return_folder.resolve()
    expected = json.loads((root / "expected-results.json").read_text())
    statements = json.loads((root / "statements.json").read_text())
    problems = []
    if set(statements) != set(expected):
        problems.append({"missing_labels": sorted(set(expected) - set(statements)),
                         "extra_labels": sorted(set(statements) - set(expected))})
    defined, modules, imports = {}, {}, {}
    for folder in [root / "lean", root / "support"]:
        for path in sorted(folder.rglob("*.lean")):
            rel = str(path.relative_to(root))
            code = lean_code(path.read_text())
            holes = re.findall(r"\b(?:sorry|admit|sorryAx)\b", code)
            if holes: problems.append(f"{rel}: unfinished proof token")
            if re.search(r"(?m)^\s*(?:unsafe\s+)?axiom\b", code):
                problems.append(f"{rel}: new axiom")
            for name, kind in declarations(code).items():
                if name in defined: problems.append(f"duplicate declaration {name}")
                defined[name] = (rel, kind)
            if path.stem in modules: problems.append(f"duplicate module filename {path.name}")
            modules[path.stem] = rel
            imports[path.stem] = re.findall(r"(?m)^import\s+(\S+)", code)
    for label, row in statements.items():
        status = row.get("status")
        if status not in {"proved", "reduced", "open"}: problems.append(f"{label}: invalid status")
        hit = defined.get(row.get("lean", ""))
        if not hit: problems.append(f"{label}: full declaration name not found")
        elif status == "open" and (hit[0] != "lean/OpenTargets.lean" or hit[1] != "def"):
            problems.append(f"{label}: open result is not a definition in OpenTargets.lean")
        elif status != "open" and hit[1] not in {"theorem", "lemma"}:
            problems.append(f"{label}: proved/reduced result is not a theorem")
        for field in ["note", "differs_from_edition"]:
            if not isinstance(row.get(field), str) or not row[field].strip():
                problems.append(f"{label}: missing {field}")
    if args.packet:
        known = set(json.loads((args.packet / "inputs/names.json").read_text()))
        for label, row in statements.items():
            for name in row.get("uses", []):
                if name not in known: problems.append(f"{label}: unknown authors' declaration {name}")
    forbidden_imports = {"EditionChallenge", "WeakenedMain", "Challenge", "CertificateChallenge",
        "ExtendedCertificateChallenge", "CellLayerChallenge", "CellLayerTheorems"}
    for module, imps in imports.items():
        for imp in imps:
            if imp in forbidden_imports: problems.append(f"{module}: forbidden solution import {imp}")
    positive = json.loads((root / "comparator.json").read_text())
    negative = json.loads((root / "comparator-control.json").read_text())
    allowed = {"propext", "Quot.sound", "Classical.choice"}
    for name, cfg in [("positive", positive), ("control", negative)]:
        if set(cfg["permitted_axioms"]) != allowed: problems.append(name + ": wrong axiom allowlist")
        if not cfg.get("theorem_names"): problems.append(name + ": no named theorem")
        if len(cfg.get("external_kernels", {})) != 4: problems.append(name + ": missing external kernel")
    if positive["challenge_module"] != negative["challenge_module"]:
        problems.append("negative control must retain the same challenge")
    if positive["solution_module"] == negative["solution_module"]:
        problems.append("negative control must use a different solution")
    result = {"check": "source_structure_only", "numbered_results": len(expected),
              "rows": len(statements), "by_status": dict(Counter(x["status"] for x in statements.values())),
              "proof_modules": len(modules), "declarations": len(defined),
              "problem_count": len(problems), "problems": problems}
    print(json.dumps(result, ensure_ascii=False, indent=2))
    raise SystemExit(bool(problems))


if __name__ == "__main__":
    main()
