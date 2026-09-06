# Probabilistic Methods in Combinatorics — formalization roadmap

## Goal

Formalize Yufei Zhao's lecture notes *Probabilistic Methods in Combinatorics*
(MIT 18.226, Fall 2022; last updated June 18, 2024) in Lean 4 + Mathlib.

This is an **independent** formalization. Contributors must not consult, copy from,
or reference Meta's ATLAS formalization of this book, in whole or in part, under any
circumstances. Work from the lecture notes and from Mathlib only.

## Route

The book has eleven chapters. We formalize them in order, in phases: a phase's
statements are committed to the protected branch first, then published as `prove`
tasks. Later phases are named here but not yet detailed — their group files are
written when the phase opens, so the plan never claims more precision than it has.

| Phase | Chapters | Group file | Status |
|---|---|---|---|
| 1 | 1 Introduction | [introduction.md](introduction.md) | statements committed |
| 1 | 2 Linearity of Expectations (§2.3) | [linearity.md](linearity.md) | statements committed |
| 2 | 2 (rest), 3 Alterations | — | not started |
| 3 | 4 Second Moment, 5 Chernoff Bound | — | not started |
| 4 | 6 Lovász Local Lemma | — | not started |
| 5 | 7 Correlation Inequalities, 8 Janson Inequalities | — | not started |
| 6 | 9 Concentration of Measure | — | not started |
| 7 | 10 Entropy | — | not started |
| 8 | 11 Containers | — | not started |

## Conventions that shape the route

**Finite probability is formalized by counting.** Chapters 1–3 argue over finite
probability spaces. Rendering those as `MeasureTheory` costs a great deal of
boilerplate and buys nothing, so their statements are counting statements:
"some colouring cuts at least half the edges" rather than "the expected number of cut
edges is `m / 2`". Genuinely measure-theoretic content — concentration, martingales,
Talagrand (Chapter 9) — will use `ProbabilityTheory` when we reach it.

**Asymptotic statements are deferred or made explicit.** Results the notes state with
`o(1)` or `≲` (Remarks 1.1.3, 1.1.7, 1.1.10; Corollary 1.4.4; Theorem 2.5.1) are not
published as tasks in the form the notes give them. Either an explicit-constant version
is stated, or the node waits until the surrounding theory is in place.

**What Mathlib already has, we do not reprove.** Sperner's theorem, the LYM inequality,
Erdős–Ko–Rado, the structural form of Turán's theorem and Markov's inequality are
upstream; they are recorded in `graph.json` as `upstream` and are never published as
tasks. Contributors should reach for them rather than reproving them.

## Reasoning log

**2026-09-06 — Toolchain: Lean `v4.33.0` + Mathlib tag `v4.33.0`. Do not bump to a
patch release.** The first pin was `v4.33.1`, and a deliberate smoke-test PR (opened by
the orchestrator, closed unmerged) showed `verify-comparator` failing at setup on a
no-op diff. Cause: `.github/workflows/verify-comparator.yml` reads `lean-toolchain` from
the PR's base SHA and checks out `leanprover/comparator` **at exactly that tag** — and
`leanprover/comparator` tags only `.0` releases. There is no `v4.33.1` tag, so the
checkout step failed, and since comparator is merge-blocking that made *every* PR
permanently unmergeable for a reason invisible in any diff.

The constraint this project now lives under: the toolchain must be a version for which
`leanprover/comparator` has a tag, i.e. an `x.y.0` release. When this pin is eventually
moved, check `gh api repos/leanprover/comparator/git/refs/tags` first and confirm
Mathlib has a matching release tag. Chosen because both `leanprover/comparator@v4.33.0`
and `mathlib4@v4.33.0` exist, and `v4.33.0` is above the `v4.27` floor where comparator
becomes a kernel-level statement check.

**2026-09-06 — Targeted imports, not `import Mathlib`.** Measured on this project:
a file importing all of Mathlib costs ~49s, the same file with targeted imports ~7s.
With one file per group of results that difference decides whether CI is minutes or
an hour. `ProbMethods/Basic.lean` carries the common imports; chapter files add what
they specifically need.

**2026-09-06 — `autoImplicit` is off.** Set in `lakefile.toml`. With it on, a typo in
a statement silently becomes a universally quantified variable, which is exactly the
failure a statement-integrity project cannot tolerate.

**2026-09-06 — Definitions live in `ProbMethods/Basic.lean`.** Every definition that
appears in a theorem *statement* is authored there by the orchestrator. Chapter files
hold statements and proofs only. This is the centralized-layer rule: those definitions
are the interface other tasks' signatures depend on, so a worker never writes one.

**2026-09-06 — Ramsey lower bounds are stated as `¬ RamseyProp n k k`, not
`n < R(k, k)`.** Defining `R(k, k)` as `sInf {n | RamseyProp n k k}` would make
`n < R(k, k)` demand that the set be nonempty — i.e. Ramsey's theorem itself — as a
side condition on top of the probabilistic argument the chapter is actually teaching.
`¬ RamseyProp n k k` is exactly what the random colouring gives, and is equivalent to
`R(k, k) > n` because `RamseyProp · k l` is upward closed. Erdős–Szekeres (Remark 1.1.5)
and the `R(k, k)` wrapper are their own nodes, for a later phase.

**2026-09-06 — The gate is validated end-to-end.** A second throwaway PR (#9, closed
unmerged) targeted a scratch declaration via a `choir/8-…` branch, so
`verify-comparator` resolved a real task target and ran its full kernel comparison
rather than no-opping. All nine checks green; comparator 2m50s, rebuild 2m42s, with the
Mathlib cache working in CI. **Still unvalidated: the merge step itself** —
`merge_pr`'s preflight and `issue-close-on-merge.yml` have never run here. The first
real contribution will exercise them.

**2026-09-06 — Validate CI before contributors arrive, not after.** The smoke test
above cost one throwaway PR and caught a defect that would otherwise have burned every
contributor's first cycle and looked like their fault. Repeat this after any change to
the toolchain, the overlay, or `verify-pr.yml`: open a no-op PR, confirm all nine checks
run and pass, close it.

**2026-09-06 — First batch held to five tasks.** Early-run calibration: `cut_half`,
`property_b_lower`, `ramsey_erdos`, `caro_wei`, `bollobas_sum`. Five different
techniques across two chapters, one of them (`bollobas_sum`) deliberately hard. Six
further nodes are stated and ready — `ramsey_alteration`, `bollobas_uniform`,
`choosable_upper`, `choosable_lower`, `caro_wei_clique`, `turan_edges` — and are
released as soon as the first batch shows the statement conventions survive contact
with a worker.
