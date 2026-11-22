#!/usr/bin/env python3
"""Check actual `#print axioms` output; missing target output is a failure."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]

def check(log: str, config: dict) -> dict:
    clean = re.sub(r"\x1b\[[0-9;]*m", "", log)
    pattern = re.compile(
        r"[‘'`]?([A-Za-z_][A-Za-z0-9_.]*)[’'`]?\s+"
        r"(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", re.S)
    declarations = {}
    for name, raw in pattern.findall(clean):
        axes = sorted(set(re.findall(r"[A-Za-z_][A-Za-z0-9_.]*", raw)))
        if name in declarations and declarations[name] != axes:
            raise ValueError(f"Conflicting axiom reports for {name}")
        declarations[name] = axes
    missing = sorted(set(config["theorem_names"]) - declarations.keys())
    allowed = set(config["permitted_axioms"])
    forbidden = {name: sorted(set(axes) - allowed) for name, axes in declarations.items()
                 if set(axes) - allowed}
    error_present = bool(re.search(r"\berror:", clean, re.I))
    ok = not missing and not forbidden and not error_present
    return {"status": "axiom_log_pass" if ok else "no_verified_pass",
            "allowed_axioms": sorted(allowed), "declarations": declarations,
            "missing_expected_targets": missing, "forbidden_axioms": forbidden,
            "lean_error_in_log": error_present,
            "log_sha256": hashlib.sha256(log.encode()).hexdigest()}

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("log", type=Path)
    parser.add_argument("--config", type=Path, default=ROOT / "axioms.json")
    args = parser.parse_args()
    try:
        result = check(args.log.read_text(), json.loads(args.config.read_text()))
    except (OSError, ValueError) as exc:
        raise SystemExit(str(exc)) from exc
    print(json.dumps(result, indent=2))
    if result["status"] != "axiom_log_pass":
        raise SystemExit(1)

if __name__ == "__main__":
    main()
