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
| §8.3 applications (triangle-free `G(n,p)`, chromatic number) | open, asymptotic |

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

## The upper bound: both blockers cleared, and the plan

The upper bound is not a correlation inequality — informally it conditions on a prefix of
the family and bounds `P(Ā_i | ⋂_{j<i} Ā_j)`. Two ingredients were missing; both now exist:

* `PMC.pweight_anticorrelate` — Harris in its **mixed** form, `P(A ∧ B) ≤ P(A) P(B)` for `A`
  increasing and `B` decreasing. Here `A` is "this bad set appears" and `B` is "none of the
  earlier ones does".
* `PMC.sum_pweight_inter_of_determinedBy` — block independence for `pweight`, the
  non-uniform analogue of `PMC.card_inter_mul_of_determinedBy`. Needed because the bad sets
  *disjoint* from `g i` live on the complementary coordinate block, where the events really
  are independent rather than merely correlated.

**Do not build a conditional-probability layer.** The right move is the one §6.1 already
made for the local lemma: keep everything multiplicative. Division by `P(⋂_{j<i} Ā_j)` is
exactly what forces case analysis on whether that probability vanishes. The per-step
estimate to prove is

    wprob (noneOf A (insert i T))
      ≤ exp (-P (A i) + ∑_{j ∈ T, g j ∩ g i ≠ ∅} P (A i ∩ A j)) · wprob (noneOf A T),

and it holds for **any** finite `T` with `i ∉ T`: split `T` into the `j` whose bad set meets
`g i` (mixed Harris) and those disjoint from it (block independence). No ordering is needed
for the step itself.

A linear order enters only in the induction, and only to make the double sum come out as
`Δ/2`: peel the **largest** element each time — the same pattern as `PMC.sum_chain_eq` in
Chapter 10 — so the remaining `T` is always a prefix and `∑_i ∑_{j < i, j ∼ i}` is the
lower-triangular half of the ordered-pair sum `Δ`.
