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
| 1 | 1 Introduction | [introduction.md](introduction.md) | **complete** (8 of 8) |
| 1 | 2 Linearity of Expectations (§2.3) | [linearity.md](linearity.md) | **complete** (3 of 3) |
| 2 | 2 (rest) | [linearity.md](linearity.md) | `szele`, `sampling`, `sumfree`, `unbalancing` all proved; §2.6 deferred |
| 3 | 3 Alterations | [alterations.md](alterations.md) | `dominating` proved; §3.3 upstream, §3.2 deferred, §3.4/§3.5 need design |
| 4 | 4 Second Moment | [second-moment.md](second-moment.md) | **§4.1 complete** (moments + variance), §4.2, §4.4 proved; §4.7 upstream; §4.3 deferred |
| 5 | 5 Chernoff Bound | [chernoff.md](chernoff.md) | **Thm 5.0.1, Cor 5.0.3, §5.1 proved**; 5.0.5/5.0.7, §5.2/§5.3 open |
| 6 | 6 Lovász Local Lemma | [local-lemma.md](local-lemma.md) | **§6.1 + §6.2 complete**: both LLL forms and hypergraph 2-colouring; §6.3–§6.6 open |
| 7 | 7 Correlation Inequalities | [correlation.md](correlation.md) | **complete in finite form**: §7.1 upstream, §7.2 proved |
| 8 | 8 Janson Inequalities | [janson.md](janson.md) | **Thm 8.1.1 lower bound proved**; upper bound needs a conditional-probability layer |
| 9 | 9 Concentration of Measure | [mathlib-survey.md](mathlib-survey.md) | **§9.1–§9.2 upstream** (Azuma–Hoeffding); §9.5 Talagrand absent |
| 10 | 10 Entropy | [mathlib-survey.md](mathlib-survey.md) | analytic groundwork upstream; discrete entropy layer absent |
| 11 | 11 Containers | — | not started |

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

### Milestone: the repository has no `sorry`

As of the Janson lower bound, every declaration in `ProbMethods/` is fully proved and every
theorem's `#print axioms` is `[propext, Classical.choice, Quot.sound]`. The two long-open
sorries (`exists_sumFree_subset`, `exists_signs_two_pow_mul_le`) were both closed by merged
PRs. This is worth keeping true: `sorry-delta` is at policy `block`, so any regression is
caught at the gate, but a `sorry` that never enters is cheaper than one that has to be
chased out.

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

**Bernoulli weights as a finite sum are the device for non-uniform arguments, and it
works.** Validated on `dominating` (§3.1), the first node whose distribution is not
uniform. Put `w X = p ^ #X * (1 - p) ^ (n - #X)` over `univ.powerset`; `Finset.prod_add`
gives `∑ w = (p + (1 - p)) ^ n = 1`, so `Finset.exists_le_of_sum_le` turns "at least as
good as the expectation" into an ordinary averaging step. No `MeasureTheory`, and `p` may
be any real — here it is `log (δ+1) / (δ+1)`. Two reusable pieces came out of it: the
subsets avoiding a fixed `B` carry weight `(1 - p) ^ #B`, and those containing a fixed `v`
carry `p`, the latter obtained by *subtracting* the former from the total rather than
building a bijection. **Expect every later chapter with a real-valued parameter to reuse
this.**

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

**Reconcile and the lease arbiter measure staleness by different clocks, and commenting
on a stale claim delays the automatic reclamation.** Validated by a dry-run dispatch of
`reconcile.yml` (`dry_run=true`, `threshold_days=0`), which correctly reported
`#2: no heartbeat label; last activity 0 days ago` — so the mechanism works, but note
*which* signal it used. `gate/reconcile/stale_claims.py` prefers a
`choir/heartbeat:YYYY-MM-DD` **label** and, when there is none, falls back to the issue's
`updated_at`. The workers here post lease **comments** and never set that label, so this
project is permanently on the `updated_at` fallback — and any comment or label edit on the
issue, including the orchestrator's own nudge, resets it. The nudge on #2 therefore pushed
its automatic reclamation out by a further day.

Consequences: `orchestrator.leases.decide_for_issue` (lease comments) and reconcile
(label / issue activity) can disagree about the same claim, and **tightening
`stale_after_days` alone will not reliably free a claim that the orchestrator keeps
touching.** Ask the holder to release *once*, then leave the issue alone.

**The daily reconcile cron also cannot be relied on for timeliness.** It is scheduled for
06:17 UTC; on 2026-09-07 it had still not fired an hour past due. The workflow is `active`,
sits on the default branch, and the repo is public and not a fork, so nothing is
misconfigured — GitHub's scheduled workflows are simply best-effort and may be delayed or
dropped. Only the `workflow_dispatch` path is dependable.

**Net effect: on this project, freeing a stale claim is a manual act.** Three independent
reasons stack up — the 7-day threshold is far longer than the 10-to-20-minute task pace,
the fallback clock resets on any issue activity, and the cron is best-effort. Do not wait
for it to resolve itself.

**When checking lease freshness, match on the `choir-lease` block, not on the word
"heartbeat".** The orchestrator's own stale-claim comment on #2 contains that word, so a
text match returns *its* timestamp and reads as though the worker is alive — which would
leave a dead lease in place indefinitely. Filter by `contains("choir-lease")` and read the
`action:` field, or just use `orchestrator.leases.decide_for_issue`.

**The board has outrun the workers.** As of the last pass there are four unclaimed tasks
(#27–#30) and no worker activity for over two hours, after ten tasks were claimed and
merged in the preceding ninety minutes. Nothing is claimed because nothing is running, not
because the tasks are too hard — so publishing more would not help, and the frontier is
deliberately not being expanded further until workers return or the overseer redirects.
Chapter 3 is the next phase to open when that happens.

**2026-09-07 — The `G(n, p)` blocker is not real, and that changes the plan for a third of
the book.** Sections 3.4, 4.1–4.4 and parts of 8 and 9 are all statements about the
Erdős–Rényi random graph, and Mathlib has no such object — which reads like a hard stop.
It is not. `G(n, p)` on a *fixed* vertex set is exactly the finite Bernoulli weight sum
`w E = p ^ #E * (1 - p) ^ (N - #E)` over `E ∈ (univ : Finset (Sym2 V)).powerset`, the same
device `dominating` (§3.1) is proved with, and `Finset.prod_add` gives that the weights
total `1`. Edge-indicator independence is the product factorisation `prod_add` already
encodes.

**What is actually hard in those sections is the asymptotics, not the probability** — every
one is phrased "with high probability as `n → ∞`". This project already has the convention
for that: state the finite-`n` inequality with explicit constants and leave the limit out.
So the ordering is: build the weighted-counting layer (`gnp_weights`, expected subgraph
counts, Chebyshev over a finite weighted space), then state explicit forms. **Chebyshev in
that form is not in Mathlib and belongs in the centralized layer**, since Chapters 4, 5 and
9 all want it.

**2026-09-07 — Weierstrass approximation (§4.7) is upstream.** Mathlib has
`bernsteinApproximation_uniform`, by the same Bernstein-polynomial argument the notes give.
Recorded in `graph.json` as `upstream`; never to be published.

**2026-09-07 — Second erratum, in Theorem 4.6.3's proof.** The notes combine the Chebyshev
bound `P ≥ 3/4` with the distinctness bound `P ≤ 2 n sqrt k 2^(-k)` and print the result as
`2 n sqrt k 2^(-k) ≤ 3/4`. That direction bounds `n` above and contradicts the stated
conclusion `n ≳ 2^k / sqrt k`; the correct combination is `3/4 ≤ 2 n sqrt k 2^(-k)`. Unlike
the Proposition 2.4.4 erratum, this one is confined to the proof — the theorem as stated is
true. Worth reporting upstream along with the other.

**2026-09-07 — Chapter 7's main theorem was already in Mathlib, and the near-miss is the
point.** `Mathlib/Combinatorics/SetFamily/FourFunctions.lean` contains `fkg` — the
Fortuin–Kasteleyn–Ginibre inequality for any log-supermodular measure on a distributive
lattice — derived from the Ahlswede–Daykin four functions theorem, which is there too,
along with Holley's inequality and Harris–Kleitman. Zhao §7.1 is upstream. I had begun
planning a `Finset`-induction proof of it before checking.

**So: search `Combinatorics/SetFamily` before planning any remaining chapter.** That one
directory holds FKG, Ahlswede–Daykin, Holley, Harris–Kleitman, Kleitman and
Kruskal–Katona. §1.2's Sperner/LYM/EKR were caught at bootstrap; this is the same lesson
recurring five chapters later, and it will recur again — Chapter 11's containers and
Chapter 10's entropy inequalities are exactly the kind of thing that may be partly present.

The bridge `PMC.pweight_fkg` is what makes the upstream result usable here: a product
measure is log-modular **with equality** (`pweight_mul_pweight`), which is the precise
sense in which independence is what FKG needs.

**2026-09-07 — Surveyed Mathlib for every remaining chapter, and it corrected a mistake of
mine.** Full results in [mathlib-survey.md](mathlib-survey.md). Two things changed:

**Theorem 5.0.5 is upstream, not unreachable.** I had recorded it as deferred because
arbitrary `[-1,1]`-valued variables give a non-finite sample space. The premise was right
and the conclusion wrong: `Mathlib/Probability/Moments/SubGaussian.lean` has **Hoeffding's
lemma** (`hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`) and **Hoeffding's inequality**
(`measure_sum_ge_le_of_iIndepFun`), which is 5.0.5. "This project's framework cannot state
it" is a fact about the framework, not about whether the mathematics exists.

**Chapter 9 is not the wall it was recorded as.** `measure_sum_ge_le_of_HasCondSubgaussianMGF`
is **Azuma–Hoeffding**, and `Probability/Martingale/` supplies the surrounding theory — so
§9.1–§9.2 are upstream in `MeasureTheory` form. Talagrand (§9.5) and the geometric sections
remain absent.

Also: Chapter 10's analytic groundwork is upstream (`negMulLog`, binary entropy, KL
divergence) but there is **no discrete Shannon entropy** in Mathlib, so §10.1–§10.4 need
that layer built first. Chapters 6, 8 and 11 are genuinely absent.

**Chapter 6 (Lovász Local Lemma) is the best next target**: absent from Mathlib, fully
expressible in the finite weighted framework already built here, and the most-cited result
in the book.

**2026-09-07 — The Lovász Local Lemma is proved** (`PMC.lovasz_local_lemma`, asymmetric
form), and it is worth recording that this chapter looked unreachable for most of the
session. It is absent from Mathlib, but the survey established that unlike Talagrand or
containers it is fully expressible in the finite weighted framework — events as `Finset`s,
`wprob` as probability, dependency as a neighbour map — and so it was work rather than
missing theory.

Two inductions: `lll_peel` on the index set, `lll_key` by strong induction on cardinality,
with the second calling the first at strictly smaller sets. **The design decision the whole
proof turned on: keep everything multiplicative.** The informal argument divides by
`P(noneOf T)`, which is not known to be positive at that point — positivity is the
conclusion. No division appears anywhere in the development.