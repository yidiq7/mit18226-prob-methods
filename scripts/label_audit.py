#!/usr/bin/env python3
"""Coverage audit against Zhao's numbered results.

Run from the repository root:

    python3 scripts/label_audit.py

A label counts as **proved** only when it is named inside a *declaration* docstring
(`/-- ... -/` immediately preceding a `theorem`/`lemma`/`def`) whose body contains no
`sorry`.  Anything weaker — a mention in a module docstring (`/-! ... -/`), a comment, or
a roadmap file — does not count.

The distinction matters: an earlier audit here counted any occurrence of a label anywhere
in the repository, including the roadmap's own *deferral* lists, and reported 82% coverage
where the strict figure was 54%.  Grepping labels measures citations, not coverage.
"""

from __future__ import annotations

import collections
import os
import re
import sys

DECL = re.compile(
    r"^\s*(?:private\s+)?(?:noncomputable\s+)?(theorem|lemma|def|abbrev|instance)"
    r"\s+([A-Za-z_][A-Za-z0-9_.']*)",
    re.M,
)
LABEL = re.compile(r"^(Theorem|Lemma|Corollary|Proposition)\s+(\d+\.\d+\.\d+)$")


def labels(path: str) -> list[tuple[str, str]]:
    out = []
    for line in open(path, encoding="utf-8"):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        m = LABEL.match(line)
        if m:
            out.append((m.group(1), m.group(2)))
    return out


def lean_sources(root: str) -> dict[str, str]:
    out = {}
    for dirpath, _, files in os.walk(root):
        for f in files:
            if f.endswith(".lean"):
                p = os.path.join(dirpath, f)
                out[p] = open(p, encoding="utf-8", errors="replace").read()
    return out


def main() -> int:
    repo = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    labs = labels(os.path.join(repo, "roadmap", "labels.txt"))
    src = lean_sources(os.path.join(repo, "ProbMethods"))

    attached: dict[str, list[tuple[str, str, bool]]] = collections.defaultdict(list)
    for path, text in src.items():
        for m in re.finditer(r"/--(.*?)-/\s*", text, re.S):
            doc, rest = m.group(1), text[m.end():]
            d = DECL.match(rest) or DECL.search(rest[:400])
            if not d:
                continue
            nxt = re.search(r"\n(/--|/-!|theorem |lemma |def |end )", rest[d.end():])
            body = rest[d.end(): d.end() + (nxt.start() if nxt else 4000)]
            has_sorry = re.search(r"\bsorry\b", body) is not None
            for kind, lab in labs:
                if lab in doc:
                    attached[lab].append(
                        (os.path.relpath(path, repo), d.group(2), has_sorry)
                    )

    proved, open_task, mentioned, absent = [], [], [], []
    for kind, lab in labs:
        hits = attached.get(lab)
        tag = kind[0] + lab
        if hits and any(not s for _, _, s in hits):
            proved.append(tag)
        elif hits:
            open_task.append(tag)
        elif any(lab in t for t in src.values()):
            mentioned.append(tag)
        else:
            absent.append(tag)

    per_ch_tot = collections.Counter(l.split(".")[0] for _, l in labs)
    per_ch_ok = collections.Counter(t[1:].split(".")[0] for t in proved)

    print(f"labels: {len(labs)}")
    print(f"  proved (declaration docstring, no sorry): {len(proved)}"
          f"  ({100 * len(proved) // len(labs)}%)")
    print(f"  statement published, proof open (sorry):  {len(open_task)}"
          f"  {' '.join(open_task)}")
    print(f"  mentioned in Lean, not a declaration:     {len(mentioned)}"
          f"  {' '.join(mentioned)}")
    print(f"  absent from Lean:                         {len(absent)}")
    print("\nproved by chapter:")
    for ch in sorted(per_ch_tot, key=int):
        print(f"  ch{ch}: {per_ch_ok[ch]}/{per_ch_tot[ch]}")
    print("\nnot proved:")
    print("  " + " ".join(open_task + mentioned + absent))
    return 0


if __name__ == "__main__":
    sys.exit(main())
