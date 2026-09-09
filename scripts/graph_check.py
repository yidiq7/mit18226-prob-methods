#!/usr/bin/env python3
"""Validate `roadmap/graph.json` against the Lean sources.

Run from the repository root:

    python3 scripts/graph_check.py

Three things are checked, all of them ways the graph can quietly stop describing the
repository:

1. **resolves** — every node carrying a `decl` names a declaration that exists in the file the
   node names;
2. **formalized is really proved** — a node with `proof: formalized` has no `sorry` in that
   declaration's body;
3. **planned is really open** — a node with `proof: planned` still has a `sorry` there (or no
   declaration at all). A stale `planned` is the failure that matters: it hides finished work,
   and it is what happens when the graph is updated by hand in the same commit as a proof;
4. **every `sorry` is owned** — each `sorry` in the sources sits in a declaration that some
   node marks `planned`, so a merged PR cannot silently leave the graph without a node.

Exits nonzero if anything fails, so it can run beside `scripts/label_audit.py`.
"""

from __future__ import annotations

import json
import os
import re
import sys

DECL = re.compile(
    r"^\s*(?:private\s+)?(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev|instance)\s+"
)


def body_of(text: str, short: str) -> str | None:
    """The source of declaration `short`, up to the next top-level declaration."""
    m = re.search(
        r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+)?(?:noncomputable\s+)?"
        r"(?:theorem|lemma|def|abbrev|instance)\s+"
        + re.escape(short)
        + r"(?![A-Za-z0-9_'])",
        text,
        re.M,
    )
    if m is None:
        return None
    rest = text[m.end():]
    nxt = re.search(r"\n(/--|/-!|@\[|theorem |lemma |def |noncomputable |private |end )", rest)
    return rest[: nxt.start()] if nxt else rest


def main() -> int:
    repo = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    nodes = json.load(open(os.path.join(repo, "roadmap", "graph.json")))["nodes"]

    unresolved, stale_planned, false_formalized, ok = [], [], [], 0
    for name, nd in nodes.items():
        decl, path, proof = nd.get("decl"), nd.get("file"), nd.get("proof")
        if not decl or not path:
            continue
        full = os.path.join(repo, path)
        if not os.path.exists(full):
            unresolved.append((name, decl, path + " (no such file)"))
            continue
        text = open(full, encoding="utf-8", errors="replace").read()
        body = body_of(text, decl.split(".")[-1])
        if body is None:
            unresolved.append((name, decl, path))
            continue
        has_sorry = re.search(r"\bsorry\b", body) is not None
        if proof == "formalized" and has_sorry:
            false_formalized.append((name, decl))
        elif proof == "planned" and not has_sorry:
            stale_planned.append((name, decl))
        else:
            ok += 1

    # reverse direction: every `sorry` in the sources is owned by a node marked `planned`
    planned_decls = {
        (nd.get("decl") or "").split(".")[-1]
        for nd in nodes.values()
        if nd.get("proof") == "planned"
    }
    orphan_sorries = []
    for dirpath, _, files in os.walk(os.path.join(repo, "ProbMethods")):
        for f in files:
            if not f.endswith(".lean"):
                continue
            full = os.path.join(dirpath, f)
            text = open(full, encoding="utf-8", errors="replace").read()
            for m in re.finditer(r"^\s*sorry\s*$", text, re.M):
                head = text[: m.start()]
                decls = re.findall(
                    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+)?(?:noncomputable\s+)?"
                    r"(?:theorem|lemma|def|abbrev|instance)\s+([A-Za-z_][A-Za-z0-9_.']*)",
                    head,
                    re.M,
                )
                owner = decls[-1] if decls else "?"
                if owner not in planned_decls:
                    rel = os.path.relpath(full, repo)
                    line = head.count("\n") + 1
                    orphan_sorries.append((owner, f"{rel}:{line}"))

    print(f"nodes: {len(nodes)}   decl-bearing and consistent: {ok}")
    for label, rows in (
        ("decl does not resolve", unresolved),
        ("claims `formalized` but has a sorry", false_formalized),
        ("claims `planned` but is proved", stale_planned),
        ("`sorry` with no `planned` node owning it", orphan_sorries),
    ):
        print(f"{label}: {len(rows)}")
        for r in rows:
            print("   ", *r)
    return 0 if not (unresolved or false_formalized or stale_planned or orphan_sorries) else 1


if __name__ == "__main__":
    sys.exit(main())
