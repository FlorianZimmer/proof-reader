#!/usr/bin/env python3
"""Add the edition modules to the pinned authors' package, without editing its Lean files.

Usage: python3 scripts/install.py /path/to/navier-stokes/lean [--check-only]
The source may be a checkout or the packet's sources/lean directory.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BEGIN = "# BEGIN N7 EDITION ADDITIONS"
END = "# END N7 EDITION ADDITIONS"


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def original_lake_bytes(path: Path) -> bytes:
    data = path.read_bytes()
    text = data.decode("utf-8")
    if BEGIN in text:
        before, extra = text.split(BEGIN, 1)
        if END not in extra or extra.split(END, 1)[1].strip():
            raise ValueError("Unexpected content after the edition Lake section")
        # The installer appends exactly two line feeds before its marker.
        if not before.endswith("\n\n"):
            raise ValueError("Malformed edition Lake section")
        return before[:-2].encode("utf-8")
    return data


def upstream_problems(destination: Path) -> list[str]:
    pins = json.loads((ROOT / "upstream-pins.json").read_text())
    problems = []
    for row in pins["members"]:
        path = destination / row["path"]
        if not path.is_file():
            problems.append("missing upstream file: " + row["path"])
            continue
        try:
            data = original_lake_bytes(path) if row["path"] == "lakefile.toml" else path.read_bytes()
        except ValueError as exc:
            problems.append(str(exc))
            continue
        if len(data) != row["bytes"] or sha(data) != row["sha256"]:
            problems.append("upstream content differs: " + row["path"])
    return problems


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("authors_lean", type=Path)
    parser.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    dest = args.authors_lean.resolve()
    problems = upstream_problems(dest)
    additions: dict[str, bytes] = {}
    for folder in [ROOT / "lean", ROOT / "support"]:
        for path in sorted(folder.rglob("*.lean")):
            if path.name in additions:
                problems.append("duplicate added module filename: " + path.name)
            additions[path.name] = path.read_bytes()
    template = (ROOT / "comparison/EditionChallenge.lean.in").read_text()
    if template.count("@CHALLENGE_PROOF@") != 2:
        problems.append("challenge template must contain exactly two proof markers")
    additions["EditionChallenge.lean"] = template.replace("@CHALLENGE_PROOF@", "by sorry").encode()
    additions["WeakenedMain.lean"] = (ROOT / "comparison/WeakenedMain.lean").read_bytes()
    pins = json.loads((ROOT / "upstream-pins.json").read_text())
    originals = {row["path"] for row in pins["members"]}
    for name, data in additions.items():
        if name in originals:
            problems.append("new module would overwrite an authors' file: " + name)
        existing = dest / name
        if existing.exists() and existing.read_bytes() != data:
            problems.append("refusing to overwrite a differing pre-existing addition: " + name)
    if problems:
        raise SystemExit(json.dumps({"ok": False, "problems": problems}, indent=2))
    if args.check_only:
        print(json.dumps({"ok": True, "upstream_files_checked": len(originals),
                          "addition_modules": len(additions), "mutated": False}, indent=2))
        return
    baseline = original_lake_bytes(dest / "lakefile.toml").decode()
    declared = set(re.findall(r'(?m)^name\s*=\s*"([^"]+)"', baseline))
    blocks = [BEGIN]
    for name in additions:
        module = Path(name).stem
        if module not in declared:
            blocks.append(f'\n[[lean_lib]]\nname = "{module}"')
    blocks.append(END)
    for name, data in additions.items():
        (dest / name).write_bytes(data)
    (dest / "lakefile.toml").write_text(baseline + "\n\n" + "\n".join(blocks) + "\n")
    comparison_dir = dest / "edition-comparison"
    comparison_dir.mkdir(exist_ok=True)
    for path in [ROOT / "comparator.json", ROOT / "comparator-control.json",
                 *sorted((ROOT / "comparison").glob("comparator-*-control.json"))]:
        (comparison_dir / path.name).write_bytes(path.read_bytes())
    remaining = upstream_problems(dest)
    if remaining:
        raise SystemExit(json.dumps({"ok": False, "post_install_problems": remaining}, indent=2))
    receipt = {"ok": True, "authors_commit": pins["commit"],
               "upstream_files_checked": len(originals), "authors_lean_files_changed": 0,
               "addition_modules": sorted(Path(x).stem for x in additions),
               "challenge_generated_separately": True,
               "build_command": "lake build EditionStatements OpenTargets EditionChallenge WeakenedMain"}
    (dest / "edition-comparison/install-receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
