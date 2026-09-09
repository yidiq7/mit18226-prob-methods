# Chapter 11 — Containers

Zhao, *Probabilistic Methods in Combinatorics*, Chapter 11.

**Not started, and the reason is not merely size.** Read off the source, every result in
§11.1 is asymptotic, and this project does not publish asymptotic statements — they have to
be deferred or restated with explicit constants first (see the conventions in
[README.md](README.md)). So Chapter 11 needs a *design decision per theorem* before any Lean
is written, which is unlike Chapters 1–8 and 10, where the statements could be taken almost
verbatim.

| Result | Statement as given | Why it needs restating |
|---|---|---|
| Thm 11.1.1 (containers for triangle-free graphs) | for every `ε > 0` there is `C > 0` such that for every `n` there is a collection `C` of graphs with `\|C\| ≤ n^(C n^(3/2))`, every member having at most `(1/4 + ε) n²` edges, containing every triangle-free graph | `∃ C` quantifier over an unspecified constant; usable, but the constant must be made explicit or left as a hypothesis |
| Thm 11.1.2 (Erdős–Stone–Simonovits) | `ex(n, H) = (1 - 1/(χ(H)-1) + o(1)) C(n,2)` | `o(1)` |
| Thm 11.1.3 | the number of `H`-free graphs on `n` vertices is `2^((1+o(1)) ex(n,H))` | `o(1)` |
| Thm 11.1.5 (Mantel in random graphs) | if `p ≫ 1/√n` then *whp* every triangle-free subgraph of `G(n,p)` has at most `(1/4 + o(1)) p n²` edges | both `≫` and `whp` |
| Conj 11.1.4 | open | not a node |

§11.2 (graph containers) and §11.3 (the hypergraph container theorem) are the machinery
Thm 11.1.1 rests on; they are where the work actually is.

## What to do first when this chapter opens

The honest entry point is **§11.2's graph container lemma in explicit finite form** — a
statement of the shape "for every `n` and every `q`, there is a family of at most `f(n,q)`
containers such that …", with `f` written out. That is a finite, non-asymptotic statement,
and Thm 11.1.1 then follows by choosing parameters. Attempting Thm 11.1.1 directly means
carrying an unspecified `C` through the whole development.

Chapter 11 also needs supersaturation for triangles (every graph with `(1/4 + ε)n²` edges
has many triangles), which is not in Mathlib and is its own piece of work.
