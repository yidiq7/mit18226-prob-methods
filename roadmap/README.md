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
| 1 | 1 Introduction | [introduction.md](introduction.md) | 3 of 8 proved; 4 published, 1 held |
| 1 | 2 Linearity of Expectations (§2.3) | [linearity.md](linearity.md) | 1 of 3 proved; 1 published, 1 held |
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
Mathlib cache working in CI. The merge step is now validated too: PR #10 merged through
`merge_pr`'s preflight, and `issue-close-on-merge.yml` closed #1 and moved it to
`choir/done`. Nothing in the gate is untested at this point.

**2026-09-06 — Validate CI before contributors arrive, not after.** The smoke test
above cost one throwaway PR and caught a defect that would otherwise have burned every
contributor's first cycle and looked like their fault. Repeat this after any change to
the toolchain, the overlay, or `verify-pr.yml`: open a no-op PR, confirm all nine checks
run and pass, close it.

**2026-09-06 — First batch held to five tasks; calibration passed, batch two
released.** The opening five (`cut_half`, `property_b_lower`, `ramsey_erdos`,
`caro_wei`, `bollobas_sum`) were five techniques across two chapters, held small so a
systematic mis-statement would surface before it was multiplied across the board. It
didn't: `cut_half` came back as a clean proof against the statement as written, using
the counting convention as intended, so the conventions survive contact with a worker.
Batch two is `ramsey_alteration` (#12), `choosable_upper` (#14) and `choosable_lower`
(#15). The other three stated nodes are held for the reason in the next entry, not for
calibration.

**2026-09-06 — A node whose `proof_uses` names an unproved theorem cannot be published
here, even though the planning playbook calls it ready.** The playbook's readiness test
asks only that a dependency be *stated* — nodes fill in any order. That is true in
general but not under this project's sorry policy. `.choir/verify.toml` leaves
`audits.sorry_delta.policy` at its default `block`, and `gate/verify/comparator.py`
adds `sorryAx` to comparator's permitted axioms **only** under policy `report`. So a
proof that invokes a still-`sorry`'d lemma carries `sorryAx` in its axiom closure and
`verify-comparator` fails it with `Illegal axiom detected` — unmergeable, for a reason
invisible in the diff, through no fault of the worker.

Consequence: `bollobas_uniform` (needs `bollobas_sum`, #5), `caro_wei_clique` (needs
`caro_wei`, #4) and `turan_edges` (needs `caro_wei_clique`) stay unpublished until the
theorems they consume are merged. Depending on a *definition* is unaffected — that is
why `choosable_upper` and `choosable_lower`, whose only dependency is
`PMC.CompleteBipartiteChoosable`, went out. **Check `proof_uses` against the inventory,
not just the graph's `statement` fields, before publishing.** If this project ever
wants genuine parallelism on chained results, the lever is switching the sorry policy
to `report` — an overseer decision, and one that changes what a green gate means.

**2026-09-06 — First contribution merged: #10, `cut_half`.** All nine checks green,
comparator 2m58s against a real target. What I checked beyond the gate: the six new
declarations are all `private` helpers about `Function.update`; the only hypothesis any
of them carries is `a ≠ b` in the half-of-colourings lemma, which is genuinely needed
and is discharged at the call site from `G.Adj a b` via `hadj.ne` — not smuggled to
make the proof close. `flipAt` is a thin wrapper on `Function.update`, so there is no
definitional gap to exploit. The argument is the intended one: sum over colourings,
exchange the order of summation, pigeonhole with `Finset.exists_le_of_sum_le`.

`verify-trust-report` listed all six helpers as `unresolved`. That is expected and not
a signal: `private` declarations get mangled `_private.…` names, so `#print axioms
PMC.flipAt` cannot resolve them. Expect this on every PR that uses private helpers —
comparator's kernel-level axiom check is what actually covers the target.

**2026-09-06 — `ramsey_erdos` (#11) and `caro_wei` (#16) merged.** Three of eleven phase-1
nodes are now proved, none of them with a new axiom.

`ramsey_erdos` counts over *all* functions `Finset (Fin n) → Bool` rather than over the
`2 ^ C(n,2)` edge-colourings. That looked wrong on first read and is in fact fine: each
bad event still has relative density `2 ^ -C(k,2)`, since `badSet` constrains `f` on
exactly the `C(k,2)` pairs inside the `k`-set and leaves every other input free. Working
over the larger, more uniform index set avoids ever constructing the set of 2-subsets as
a `Fintype`. Worth remembering before anyone "fixes" it.

`caro_wei` took the Remark 2.3.4 derandomization, not the random-ordering argument, via a
private lemma generalizing the bound to an induced subgraph (`d_t u` counting only
neighbours inside `t`) so that strong induction on `t` goes through. This is the
generalize-then-induct shape; expect it again on `turan_edges`.

**2026-09-06 — `caro_wei_clique` (#17) published, unblocked by #16.** Its `proof_uses`
dependency is now a real theorem rather than a `sorry`, so it can merge. Remaining held:
`bollobas_uniform` (waiting on `bollobas_sum`, #5) and `turan_edges` (waiting on
`caro_wei_clique`, #17). The frontier now unblocks itself as each chain link lands — no
action needed beyond publishing the successor when its dependency merges.

**2026-09-06 — `choosable_upper` (#13) merged.** Notable for adding *no* new declarations:
the whole union-bound argument sits inline in the pre-stated theorem, so comparator's
kernel check covers all of it and there is no worker-authored statement to audit. When a
node can be closed this way it is the cheapest possible thing to review — worth
preferring in task hints where the argument is short enough to inline.

**2026-09-06 — Publishing bug: `choosable_upper` was published twice, as #13 and #14.**
The publishing script created #13, then crashed on a formatting bug in its own progress
`print` (a label enum's `.value` is an `int`, not a `str`). On the re-run only the
already-confirmed node was removed from the batch, so `choosable_upper` went out a second
time. #14 was closed as a duplicate, `choir/invalid`; it was never claimed, so no work was
lost, and #13 is the live task.

**The lesson, for whoever publishes next: creating an issue is not idempotent, so before
re-running a partially-failed publish, list the board and diff it against the batch.**
Never infer what landed from how far the script's output got — the crash here happened
*after* the API call that mattered. Better still, do the label edits in the same call that
creates the issue, or verify by target_decl rather than by issue number.
