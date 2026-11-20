"""Render one certificate tree JSON (from ExtractZeta.lean) as an indented text outline.

Each line: label from the parent (the field or hypothesis this proof fills), node kind, lemma,
and for enclosures the centre ± radius as decimals. Shared nodes are expanded once and then
referenced as "(see #id)". Usage: outline.py TREE.json [--depth N] [--max-lines N]
"""
import argparse
import json
from fractions import Fraction


def dec(neg, n, d, digits=12):
    if d == 0:
        return "?"
    x = Fraction(n, d) * (-1 if neg else 1)
    return f"{float(x):.{digits}g}"


def encl(e):
    if not e:
        return ""
    return f"{dec(e['neg'], e['cn'], e['cd'])} ± {dec(False, e['rn'], e['rd'], 3)}"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("tree")
    ap.add_argument("--depth", type=int, default=40)
    ap.add_argument("--max-lines", type=int, default=4000)
    args = ap.parse_args()
    doc = json.load(open(args.tree))
    tree = doc["tree"]
    nodes = {n["id"]: n for n in tree["nodes"]}
    print(f"# {doc['method']} row {doc['row']}  source={doc['source']}  ctor={doc['certificate_ctor']}")
    print(f"# endpoints {json.dumps(doc['endpoints'])}")
    print(f"# {tree['node_count']} nodes; kinds {json.dumps(tree['kinds'])}; walk {doc['walk_ms']} ms\n")
    seen = set()
    lines = 0

    def show(i, label, depth):
        nonlocal lines
        if lines >= args.max_lines:
            return
        n = nodes[i]
        pad = "  " * depth
        lab = f"{label}: " if label else ""
        if i in seen:
            print(f"{pad}{lab}(see #{i} {n['head']})")
            lines += 1
            return
        seen.add(i)
        val = ""
        if n.get("re") and n.get("im"):
            val = f"  [re {encl(n['re'])}; im {encl(n['im'])}]"
        elif n.get("re"):
            val = f"  [{encl(n['re'])}]"
        subj = f"  of {n['subject']}" if n.get("subject") else ""
        red = f"  (kernel evaluates {n['reduces']})" if n.get("reduces") else ""
        print(f"{pad}{lab}#{i} {n['kind']} {n['head']}{val}{subj}{red}")
        lines += 1
        if n["kind"] in ("kernel",) or not n.get("subject"):
            if n["kind"] == "kernel" or depth < 2:
                print(f"{pad}    ⊢ {n['statement']}")
                lines += 1
        if depth >= args.depth:
            if n["children"]:
                print(f"{pad}  … {len(n['children'])} children not shown")
                lines += 1
            return
        labels = n.get("labels") or [""] * len(n["children"])
        for c, l in zip(n["children"], labels):
            show(c, l, depth + 1)

    show(tree["root"], "", 0)
    if lines >= args.max_lines:
        print(f"\n… stopped at {args.max_lines} lines")


if __name__ == "__main__":
    main()
