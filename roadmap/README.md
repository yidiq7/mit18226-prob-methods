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
| 1 | 1 Introduction | [introduction.md](introduction.md) | 7 of 8 proved; `property_b_lower` claimed |
| 1 | 2 Linearity of Expectations (§2.3) | [linearity.md](linearity.md) | **complete** (3 of 3) |
| 2 | 2 (rest) | [linearity.md](linearity.md) | **open**: `szele` stated; §2.6 deferred |
| 3 | 3 Alterations | — | not started |
| 4 | 4 Second Moment, 5 Chernoff Bound | — | not started |
| 5 | 6 Lovász Local Lemma | — | not started |
| 6 | 7 Correlation Inequalities, 8 Janson Inequalities | — | not started |
| 7 | 9 Concentration of Measure | — | not started |
| 8 | 10 Entropy | — | not started |
| 9 | 11 Containers | — | not started |

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

Compressed 2026-09-06. Per-node merge narratives have been dropped — `graph.json` carries
status and git history carries the diffs. What remains is everything a restarted
orchestrator would otherwise have to rediscover.

### Hard constraints

**Toolchain must be an `x.y.0` release: Lean `v4.33.0` + Mathlib `v4.33.0`.** The first
pin was `v4.33.1`, and a smoke-test PR showed `verify-comparator` failing at setup on a
no-op diff. `verify-comparator.yml` checks out `leanprover/comparator` at exactly the tag
in `lean-toolchain`, and that repo tags only `.0` releases — so there is no `v4.33.1` tag,
the checkout step failed, and since comparator is merge-blocking *every* PR became
permanently unmergeable for a reason invisible in any diff. Before moving this pin, check
`gh api repos/leanprover/comparator/git/refs/tags` and confirm Mathlib has a matching
release tag. `v4.33.0` is above the `v4.27` floor where comparator becomes a kernel-level
statement check.

**A node whose `proof_uses` names an unproved theorem cannot be published here**, even
though `orchestrator-planning.md`'s readiness test calls it ready — that test asks only
that a dependency be *stated*. `.choir/verify.toml` leaves `audits.sorry_delta.policy` at
the default `block`, and `gate/verify/comparator.py` adds `sorryAx` to comparator's
permitted axioms **only** under policy `report`. So a proof invoking a still-`sorry`'d
lemma carries `sorryAx` in its axiom closure and comparator fails it with
`Illegal axiom detected` — unmergeable, invisible in the diff, and not the worker's fault.
**Check `proof_uses` against the inventory before publishing, not just the graph's
`statement` fields.** Depending on a *definition* is unaffected. Switching the sorry policy
to `report` would buy parallelism on chained results at the cost of what a green gate
means; that is an overseer decision.

**`choir/invalid` does not mean "the orchestrator rejected this."** It means *failed intake
validation, retry pending*: `issue-intake.yml` fires on `labeled` and its `if` matches
`choir/invalid` as well as `choir/available`, so labelling a well-formed task `choir/invalid`
makes intake re-validate it, find it fine, and hand it back as `choir/available`. **To
retire a task, close it and *remove* `choir/available`** — removal fires `unlabeled`, which
intake does not listen for, and an issue with no lifecycle label is skipped by
`sync_lease_labels` too.

**`autoImplicit` is off** (`lakefile.toml`). With it on, a typo in a statement silently
becomes a universally quantified variable — exactly the failure a statement-integrity
project cannot tolerate.

**Definitions that appear in a theorem statement live in `ProbMethods/Basic.lean`,**
authored by the orchestrator. Chapter files hold statements and proofs only. Those
definitions are the interface other tasks' signatures depend on, so a worker never writes
one.

**Targeted imports, not `import Mathlib`.** Measured here: a file importing all of Mathlib
costs ~49s, the same file with targeted imports ~7s. With one file per group of results
that difference decides whether CI is minutes or an hour.

### Practices that paid off

**Validate CI before contributors arrive, not after.** Two throwaway PRs (#6/#7, then #9
targeting a scratch declaration through a `choir/8-…` branch so comparator resolved a real
target) cost nothing and caught the toolchain defect above, which would otherwise have
burned every contributor's first cycle and looked like their fault. Repeat after any change
to the toolchain, the overlay, or `verify-pr.yml`. The merge path is validated too: PR #10
went through `merge_pr`'s preflight and `issue-close-on-merge.yml` moved #1 to
`choir/done`.

**Check every centralized definition numerically before committing it.** The statement
layer gets *no* gate check, and a wrong definition makes every theorem about it vacuously
true — the one failure the whole verification stack cannot catch. `beats`/`hamiltonPaths`
were confirmed by reproducing the counting identity at two sizes (`96 = 3! * 2^4` over the
64 tournaments on 3 vertices, `8 = 2! * 2^2` over the 8 on 2) plus antisymmetry; `SumFree`
against six known examples; the §2.5 bound exhaustively against every `±1` matrix for
`n ≤ 4`, where it turns out to be *tight* at `n = 1, 2`.

**Publishing an issue is not idempotent.** `choosable_upper` went out twice, as #13 and
#14, because the publish script crashed on a formatting bug in its own progress `print`
*after* the API call that mattered, and the re-run dropped only the node whose success had
been printed. #14 was closed unclaimed, nothing lost. **Before re-running a partially
failed publish, list the board and diff it by `target_decl`** — and do not infer what
landed from how far the output got. When auditing, check the audit actually ran: the first
duplicate scan returned "none" only because every row had errored.

### What contributions look like here

**Counting over a larger uniform space is the idiom, not a mistake.** `ramsey_erdos` counts
over all functions `Finset (Fin n) → Bool` and `ramsey_alteration` over all subsets of
`Sym2 (Fin n)` — both bigger than the `2^C(n,2)` genuine edge-colourings, diagonal
included. Sound because each bad event keeps its relative density, and it avoids building a
`Fintype` of 2-subsets. **Two contributors reached for this independently**, and the
tournament encoding in §2.1 follows it deliberately. Do not let anyone "fix" it.

**`verify-trust-report` lists `private` helpers as `unresolved`, and that is expected** —
private names are mangled to `_private.…`, so `#print axioms PMC.foo` cannot resolve them.
Comparator's kernel-level axiom check is what actually covers the target.

**The cheapest PRs to review add no new declarations at all** — `choosable_upper`,
`choosable_lower`, `caro_wei_clique` and `turan_edges` each put the whole argument inline in
the pre-stated theorem, leaving nothing worker-authored to audit. Worth preferring in task
hints when the argument is short enough to inline.

### Errata in the source

**Proposition 2.4.4 is printed for `n ≥ 4` and is false there.** On four vertices the
extremal tetrahedron-free 3-graph has `3` of the `4` triples — drop any one and no
tetrahedron survives — while `(7/10) * C(4,3) = 2.8`. Verified by brute force. Our
statement requires `5 ≤ n`, which is what the sampling argument needs anyway. Worth
reporting via the errata form in the notes' preface.

### Open items for the overseer

**`reconcile.stale_after_days = 7` is mismatched to this project's pace.** #2 was claimed
at 20:10:53Z with its last heartbeat at 20:11:07Z and nothing since, while nine other tasks
were claimed and merged inside 10–20 minutes each over the same hour. A dead worker session
therefore holds a phase-1 node for a week. The default suits multi-month formalizations.
The holder was asked to release; the lease was **not** overridden, and
`.choir/project.toml` was **not** edited, because it is policy.

**The board has outrun the workers.** As of the last pass there are four unclaimed tasks
(#27–#30) and no worker activity for over two hours, after ten tasks were claimed and
merged in the preceding ninety minutes. Nothing is claimed because nothing is running, not
because the tasks are too hard — so publishing more would not help, and the frontier is
deliberately not being expanded further until workers return or the overseer redirects.
Chapter 3 is the next phase to open when that happens.
