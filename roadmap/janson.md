# Chapter 8 — Janson Inequalities

Zhao, *Probabilistic Methods in Combinatorics*, Chapter 8.

## The setting, and why it is reachable

Janson's inequalities are about a random subset `S` of a finite ground set, each element
kept independently with its own probability, and a family of "bad" sets `g : ι → Finset α`
with events `A i = "g i ⊆ S"`. In the notes the ground set is the edge set of `K_n` and the
`g i` are copies of a fixed graph, so `A i` is "this copy appears in `G(n,p)`".

That is exactly `PMC.pweight` over `α`, so Chapter 8 needs no new probability layer — the
same observation that dissolved the `G(n,p)` blocker for §3.4 and §4.1–4.4. Mathlib has no
Janson inequality of any kind; it does have the four functions theorem, which is what the
lower bound ultimately rests on.

The theorem sandwiches the probability that no bad set appears:

```
∏ i, (1 - P (A i))   ≤   P (no A i occurs)   ≤   exp (-μ + Δ/2)
```

## Status

| Piece | Status |
|---|---|
| `PMC.pweight_fkg_anti` — FKG for *decreasing* functions | proved |
| `PMC.pweight_correlate_anti` — Harris for two decreasing events | proved |
| `PMC.pweight_correlate_anti_family` — Harris for a whole family | proved |
| `PMC.sum_pweight_not_superset` — `P(¬ B ⊆ S) = 1 - ∏_{x ∈ B} p x` | proved |
| `PMC.janson_lower` — **Theorem 8.1.1, lower bound** | proved |
| Theorem 8.1.1, upper bound `exp (-μ + Δ/2)` | open |
| §8.2 (extended Janson, `Δ ≥ μ` regime) | open |
| **Thm 7.2.2 / §8.3's lower bound** (`prob_not_hasTriangle_ge`) | proved |
| **Janson for triangles** (`probTriangleFree_le_exp`) | proved |
| **Cor 8.1.7** — `P(triangle-free) → e^{-c³/6}` | proved |
| §8.3's chromatic number application | open, asymptotic |

## The lower bound: how it went

`PMC.janson_lower` says `∏ i, (1 - ∏ x ∈ g i, p x) ≤ P(no g i is contained in S)`, with **no
hypothesis relating the `g i` to each other** — overlapping bad sets are the interesting
case and the bound holds regardless. The reason is that each event "`g i` is *not*
contained in `S`" is *decreasing*, and decreasing events are positively correlated, so
correlation only ever helps.

The one piece of new infrastructure was the decreasing form of FKG. It came for free from
the **order dual**: `Finset α` and `(Finset α)ᵒᵈ` are both distributive lattices, and the
log-supermodularity that `pweight` satisfies,

```
pweight p T * pweight p U = pweight p (T ∩ U) * pweight p (T ∪ U),
```

is an *equality* and therefore symmetric in `⊓` and `⊔`. So Mathlib's `fkg` transports to
the dual verbatim, where `Monotone` means `Antitone`. Worth remembering: when a hypothesis
is stated as an equality rather than an inequality, order-reversal is usually free.

## §8.1 for triangles, and Corollary 8.1.7 — proved

`ProbMethods/Chapter08/JansonTriangle.lean`.

`PMC.probTriangleFree_le_exp`: `P(G(n,p) triangle-free) ≤ exp(-C(n,3)p³ + 3n C(n,3)p⁵/2)`.
`PMC.janson` supplies `exp(-μ + Δ/2)` for an arbitrary family; the work is computing the two
quantities for the `C(n,3)` potential triangles. `μ = C(n,3)p³` since each spans three edges,
and `Δ ≤ 3n C(n,3) p⁵` because two distinct triples share an edge exactly when they share two
vertices, in which case they span `6 - 1 = 5` edges (`PMC.card_spannedEdges_union`), and each
triple has at most `3n` such partners (`PMC.card_partners_le`, shared with Chapter 4's
variance).

`PMC.tendsto_probTriangleFree_exp` is **Corollary 8.1.7**:

    P(G(n, c/n) triangle-free) → e^{-c³/6}.

Both brackets converge to it: `C(n,3)p³ → c³/6` and `3n C(n,3)p⁵ = 3c⁵·C(n,3)/n⁴ → 0` for the
Janson side, and for the Harris side `(1-p³)^{C(n,3)} ≥ exp(-C(n,3)p³/(1-p³))`, whose exponent
has the same limit.

**No logarithms and no series.** Both bracketing inequalities for `1 - u` are
`Real.add_one_le_exp`: `1 - u ≤ exp(-u)` directly, and `exp(-u/(1-u)) ≤ 1 - u` by applying it
at `u/(1-u)` and multiplying by `exp(-u/(1-u))`. That is what keeps the whole corollary
elementary — the temptation is to take logs and expand, which needs an error term.

The index type is `Fin (C(n,3))` with an explicit enumeration, not the triples themselves:
`PMC.janson`'s upper half needs a linear order on the index, and transporting one onto
`Finset (Fin n)` would bring its own `DecidableEq` and break every `filter` in the statement —
the trap `Chapter10/Shearer.lean` documents.

Checked by simulation at `c = 1` and `c = 2`, `n = 10, 20, 40`: the simulated probability sits
between the two brackets throughout and both brackets close on `e^{-c³/6}` (at `c = 1`,
`n = 40`: `0.857 ≤ 0.861 ≤ 0.862` against the limit `0.8465`).

## The upper bound — proved

`PMC.janson_upper`, and `PMC.janson` states both halves together in the notes' form. The
decision that made it tractable was a negative one: **no conditional-probability layer.**
The informal proof divides by `P(⋂_{j<i} Ā_j)`, and that division is the only thing that
would force a case analysis on whether the prefix has positive probability. Stating each
step as `P(D ∩ Āᵢ) ≤ c · P(D)` avoids it entirely — the same choice §6.1 made for the local
lemma, and it was right both times.

The pieces:

* `PMC.janson_step` — the contraction. It holds for **any** finite `T` with `i ∉ T` and
  needs no ordering: split `T` into the `j` whose bad set meets `g i`, handled by mixed
  Harris (`PMC.wprob_pweight_anticorrelate`, since `Aᵢ ∩ A_j` is increasing and "none of the
  far part occurs" is decreasing), and those disjoint from it, handled by block independence
  (`PMC.sum_pweight_inter_of_determinedBy`, since they live on the complementary coordinate
  block and so are genuinely independent rather than merely correlated). The union bound in
  between is `PMC.wprob_le_of_subset_union`.
* `PMC.janson_prod_le` — the induction. Peel the **largest** index each time, so the peeled
  set is always a prefix; the same pattern as `PMC.sum_chain_eq` in Chapter 10.
* `PMC.jansonFactor_le_exp` — `1 + x ≤ exp x`, turning the product into `exp(-μ + …)`.
* `PMC.two_mul_sum_lt_eq_sum_ne` — the lower-triangular sum is exactly `Δ/2`. Worth having
  so the statement matches the notes rather than an equivalent-but-different convention.

Checked numerically at six configurations, several of them tight (`0.625` against `0.687`),
which pins down both the exponent and the lower-triangular convention.

## Still open in Chapter 8

§8.2 (the extended Janson inequality, for the regime `Δ ≥ μ`) and §8.3's applications
(triangle-free `G(n,p)`, the chromatic number), which are asymptotic and need the project's
explicit-constant treatment.

## Theorem 8.1.8 (Janson inequality II) — proved

`ProbMethods/Chapter08/JansonII.lean`. If `μ ≤ Δ` then `P(X = 0) ≤ exp(-μ²/(2Δ))`. Janson I is
strong only when `Δ = o(μ)`; this covers the other regime.

The notes' proof is a **sampling** argument, and both of its ingredients were already here:

* `PMC.janson_prod_le` was stated for an arbitrary subfamily, so `PMC.janson_upper_sub` —
  Janson I for a subfamily — needed no new work at all;
* the random subfamily is `PMC.bweight` on `Finset ι`, whose first moment is
  `PMC.wmean_bweight_linear` and whose second is `PMC.sum_bweight_mem_pair`.

What had to be added was the bookkeeping between them: writing `Δ/2` as a **single sum over a
`Finset` of pairs** (`PMC.jPairs`) rather than a nested double sum, after which the second
moment is a sum swap and `q^{#{i,j}} = q²` for each pair — distinct because the second index
is strictly smaller. `μ ≤ Δ` is exactly what makes the sampling probability `q = μ/Δ` at most
one, and `PMC.exists_le_wmean` supplies the subfamily at least as good as the average.

**This gap was found by auditing the source label by label**, not by reading the chapter
status line, which said "both bounds" and meant Theorem 8.1.2 and Remark 8.1.3.
