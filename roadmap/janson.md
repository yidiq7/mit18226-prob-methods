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

## The upper bound is a different argument

The upper bound is not a correlation inequality. It conditions on a prefix of the family —
`P(Ā_i | ⋂_{j<i} Ā_j)` — and bounds each conditional probability using Harris *and* a
union bound over the `j < i` that share an element with `i`. Two things it needs that the
lower bound did not:

* conditional probability in the finite weighted framework (a definition, plus the chain
  rule as a `Finset.prod_range_succ`-style telescoping);
* `1 - t ≤ exp (-t)`, which is `Real.add_one_le_exp` — already used in §6.1.

Neither is deep, but together they are a session's work, and the conditional-probability
layer would be new. It is the natural next Chapter 8 task.
