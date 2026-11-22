#!/usr/bin/env python3
"""Precompile and run the positive comparison and each weaker control.

Use a trusted Comparator/lean4export installation compatible with Lean 4.33.1,
as in the existing proof-reader Actions workflow. The runner does not install
or replace kernels. Missing tools and compilation errors fail the run.
Run ``python3 scripts/run_comparator.py --self-test`` for the mocked-log tests.
"""
import argparse
import json
import re
import subprocess
import unittest
from pathlib import Path


TARGETS = ["NavierStokes.theorem_1_1_space", "NavierStokes.conditional_main"]
KERNELS = {"Lean paranoid", "con-leche", "con-ron", "nanoda"}
AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
SPECS = [("positive", "comparator.json", False, TARGETS),
         ("space-control", "comparator-space-control.json", True, TARGETS[:1]),
         ("main-control", "comparator-main-control.json", True, TARGETS[1:])]


def parse_log(log):
    """Recognize Comparator's actual rejection, not a Lean type error."""
    clean = re.sub(r"\x1b\[[0-9;]*m", "", log)
    mismatches = sorted(set(re.findall(
        r"Challenge and solution theorem statement do not match:\s*"
        r"[‘'`\"]([A-Za-z_][A-Za-z0-9_.]*)[’'`\"]", clean)))
    infrastructure = bool(re.search(
        r"(?im)(?:command not found|no such file|unknown module|build failed|"
        r"Lean exited with code|uncaught exception|"
        r"^[^\n]*\.lean:\d+:\d+:\s*error:|"
        r"^\s*error:\s*(?:type mismatch|failed to|unknown|invalid|unsolved goals))",
        clean))
    return mismatches, infrastructure


def evaluate_result(name, returncode, log, negative, expected_names):
    mismatches, infrastructure = parse_log(log)
    exact_mismatch = set(mismatches) == set(expected_names)
    passed = (returncode != 0 and exact_mismatch and not infrastructure) if negative else (
        returncode == 0 and not mismatches and not infrastructure)
    return {"case": name,
            "expected": "statement mismatch" if negative else "acceptance",
            "expected_theorems": expected_names,
            "exit_code": returncode,
            "statement_mismatch_theorems": mismatches,
            "infrastructure_error_observed": infrastructure,
            "passed": passed}


def validate_configs(configs):
    """Keep both controls on the fixed challenge and all four external kernels."""
    positive = configs["positive"]
    if not isinstance(positive, dict):
        raise ValueError("positive: configuration must be a JSON object")
    for name, _, negative, targets in SPECS:
        cfg = configs[name]
        if not isinstance(cfg, dict):
            raise ValueError(f"{name}: configuration must be a JSON object")
        if cfg.get("theorem_names") != targets:
            raise ValueError(f"{name}: expected theorem_names {targets}")
        if cfg.get("challenge_module") != positive.get("challenge_module"):
            raise ValueError(f"{name}: control must retain the positive challenge")
        if negative and cfg.get("solution_module") == positive.get("solution_module"):
            raise ValueError(f"{name}: control must use a different solution module")
        if cfg.get("solution_module") == cfg.get("challenge_module"):
            raise ValueError(f"{name}: a challenge cannot serve as its own solution")
        if set(cfg.get("permitted_axioms", [])) != AXIOMS:
            raise ValueError(f"{name}: incorrect axiom allowlist")
        kernels = cfg.get("external_kernels", {})
        if not isinstance(kernels, dict) or set(kernels) != KERNELS or kernels != positive.get("external_kernels"):
            raise ValueError(f"{name}: all four identical external-kernel commands are required")
        if any(not isinstance(cmd, list) or not cmd or
               any(not isinstance(arg, str) or not arg for arg in cmd)
               for cmd in kernels.values()):
            raise ValueError(f"{name}: invalid external-kernel command")
        for field in ["challenge_module", "solution_module"]:
            if not isinstance(cfg.get(field), str) or not re.fullmatch(
                    r"[A-Za-z_][A-Za-z0-9_.]*", cfg[field]):
                raise ValueError(f"{name}: invalid {field}")


def run_command(command, destination):
    try:
        run = subprocess.run(command, cwd=destination, text=True,
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        return run.returncode, run.stdout
    except OSError as exc:
        return -1, f"Unable to start command: {exc}\n"


def finish(output, receipt):
    (output / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))
    raise SystemExit(0 if receipt["all_passed"] else 1)


def self_test():
    """Control parsing must reject build errors, missing tools and wrong targets."""
    class LogTests(unittest.TestCase):
        def test_rejection_cases(self):
            mismatch = ("Challenge and solution theorem statement do not match: "
                        "'NavierStokes.theorem_1_1_space'\n")
            cases = [
                (1, mismatch, True),
                (1, "\x1b[31m" + mismatch + "\x1b[0m", True),
                (0, mismatch, False),
                (1, mismatch.replace(TARGETS[0], TARGETS[1]), False),
                (1, "WeakenedMain.lean:4:2: error: type mismatch\n", False),
                (1, mismatch + "WeakenedMain.lean:4:2: error: type mismatch\n", False),
                (127, "con-ron: command not found\n", False),
                (1, "", False),
            ]
            for code, log, expected in cases:
                with self.subTest(code=code, log=log):
                    self.assertEqual(evaluate_result(
                        "space-control", code, log, True, TARGETS[:1])["passed"], expected)

        def test_positive_must_succeed(self):
            self.assertTrue(evaluate_result("positive", 0, "Accepted\n", False, TARGETS)["passed"])
            self.assertFalse(evaluate_result("positive", 1, "Accepted\n", False, TARGETS)["passed"])
            self.assertFalse(evaluate_result(
                "positive", 0, "con-ron: command not found\n", False, TARGETS)["passed"])

    suite = unittest.defaultTestLoader.loadTestsFromTestCase(LogTests)
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    raise SystemExit(0 if result.wasSuccessful() else 1)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("authors_lean", nargs="?", type=Path)
    ap.add_argument("--comparator", help="Absolute path to the trusted Comparator executable")
    ap.add_argument("--lake", default="lake")
    ap.add_argument("--output", type=Path, default=Path("comparator-results"))
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()
    if args.self_test:
        self_test()
    if args.authors_lean is None or args.comparator is None:
        ap.error("authors_lean and --comparator are required unless --self-test is used")
    dest = args.authors_lean.resolve()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    receipt = {"all_passed": False, "precompilation": None, "results": []}
    try:
        configs = {name: json.loads((dest / "edition-comparison" / filename).read_text())
                   for name, filename, _, _ in SPECS}
        validate_configs(configs)
    except (OSError, ValueError, TypeError, KeyError) as exc:
        receipt["configuration_error"] = str(exc)
        finish(out, receipt)

    modules = sorted({cfg[field] for cfg in configs.values()
                      for field in ["challenge_module", "solution_module"]})
    build_command = [args.lake, "build", *modules]
    code, log = run_command(build_command, dest)
    (out / "precompile.log").write_text(log)
    _, infrastructure = parse_log(log)
    receipt["precompilation"] = {"command": build_command, "modules": modules,
                                 "exit_code": code, "passed": code == 0 and not infrastructure}
    if not receipt["precompilation"]["passed"]:
        receipt["abort_reason"] = "Challenge and solution modules did not all compile successfully."
        finish(out, receipt)

    receipt["external_kernels"] = sorted(KERNELS)
    receipt["challenge_module"] = configs["positive"]["challenge_module"]
    for name, filename, negative, targets in SPECS:
        command = [args.lake, "env", str(Path(args.comparator).resolve()),
                   str(dest / "edition-comparison" / filename)]
        code, log = run_command(command, dest)
        (out / (name + ".log")).write_text(log)
        receipt["results"].append(evaluate_result(name, code, log, negative, targets))
    receipt["all_passed"] = all(result["passed"] for result in receipt["results"])
    finish(out, receipt)


if __name__ == "__main__":
    main()
