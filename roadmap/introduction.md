# Chapter 1 — Introduction

The chapter introduces the probabilistic method through four families of results.
All statements live under the `PMC` namespace; definitions are in
`ProbMethods/Basic.lean`.

## Large bipartite subgraph (§1.0)

### cut_half
`PMC.exists_cut_two_mul_card_edgeFinset_le` — Theorem 1.0.1.

Every graph with `m` edges has a bipartite subgraph with at least `m / 2` edges.

Formalized as a max-cut bound: there is a two-colouring `c : V → Bool` with
`#G.edgeFinset ≤ 2 * #(cutEdges G c)`, where `cutEdges G c` collects the edges whose
endpoints get different colours. Those edges are precisely the edges of a bipartite
subgraph, so this is the notes' statement with the subgraph made explicit and the
division by 2 cleared.

Zhao's proof: colour each vertex black or white independently and uniformly. Each edge
is cut with probability `1 / 2`, so `E[#cut] = m / 2` by linearity of expectation, and
some colouring attains at least the mean. In Lean the averaging step is a `Finset` sum
over all `2 ^ n` colourings; a purely extremal proof (take a colouring maximizing the
cut, and observe every vertex has at least half its edges crossing) is equally
acceptable, and may well be shorter.

## Lower bounds to Ramsey numbers (§1.1)

`PMC.RamseyProp n k l` encodes a red/blue colouring of `Kₙ` as a simple graph `G` on
`Fin n`: red = adjacent, blue = non-adjacent. So a red `K_k` is `¬ G.CliqueFree k` and a
blue `K_l` is `¬ Gᶜ.CliqueFree l`.

### ramsey_erdos
`PMC.not_ramseyProp_of_two_mul_choose_lt` — Theorem 1.1.2 (Erdős 1947).

If `C(n,k) · 2^(1 - C(k,2)) < 1` then `R(k,k) > n`. The hypothesis is stated over `ℕ`
as `2 * n.choose k < 2 ^ k.choose 2`, which is the same inequality with denominators
cleared.

Zhao's proof: colour the edges uniformly at random. Each of the `C(n,k)` vertex `k`-sets
is monochromatic with probability `2^(1 - C(k,2))`; the union bound makes the chance
that some `k`-set is monochromatic less than 1, so a good colouring exists. The Lean
proof is a counting argument: the number of colourings admitting a monochromatic `k`-set
is at most `C(n,k) · 2 · 2^(C(n,2) - C(k,2))`, which the hypothesis puts below
`2^(C(n,2))`, the total number of colourings.

### ramsey_alteration
`PMC.exists_cliqueFree_of_alteration` — Theorem 1.1.6.

`R(k,k) > n - C(n,k) · 2^(1 - C(k,2))`, stated as: some `m` at least that large carries
a colouring of `K_m` with no monochromatic `K_k`.

Zhao's proof (the alteration/deletion method): colour `Kₙ` at random, then delete one
vertex from every monochromatic `K_k`. The expected number of such cliques is
`C(n,k) · 2^(1 - C(k,2))`, so with positive probability at least
`n - C(n,k) · 2^(1 - C(k,2))` vertices survive, and by construction nothing
monochromatic remains.

Theorem 1.1.9 (Spencer's bound via the local lemma) belongs with Chapter 6 and is not a
node here; Remarks 1.1.3, 1.1.7 and 1.1.10 are asymptotic optimizations we do not
formalize in the form given.

## Set systems (§1.2)

Sperner's theorem (1.2.2), the LYM inequality (1.2.3) and Erdős–Ko–Rado (1.2.9) are
already in Mathlib as `IsAntichain.sperner`,
`Finset.lubell_yamamoto_meshalkin_inequality_sum_inv_choose` and `Finset.erdos_ko_rado`.
They are `upstream` nodes; do not reprove them.

### bollobas_sum
`PMC.sum_inv_choose_le_one` — Theorem 1.2.6 (Bollobás 1965).

Given finite sets with `A i ∩ B i = ∅` for every `i` and `A i ∩ B j ≠ ∅` for `i ≠ j`,
`∑ i, 1 / C(|A i| + |B i|, |A i|) ≤ 1`.

Zhao's proof modifies the LYM argument: take a uniformly random ordering of
`⋃ i (A i ∪ B i)` and let `E i` be the event that all of `A i` precedes all of `B i`,
which has probability `1 / C(|A i| + |B i|, |A i|)`. The hypotheses force the `E i` to be
pairwise disjoint — if `E i` and `E j` both held, the interleaving of `A i, B i, A j, B j`
would contradict one of `A i ∩ B j ≠ ∅`, `A j ∩ B i ≠ ∅` — so the probabilities sum to at
most 1. Note the events are over orderings of the *union*, whose size varies with `i`;
the clean Lean route is to fix a single ground set containing every `A i ∪ B i` and count
linear orders of it.

### bollobas_uniform
`PMC.card_le_choose_of_two_families` — Theorem 1.2.4.

The `r`-uniform / `s`-uniform case: `m ≤ C(r + s, r)`. Every summand in `bollobas_sum`
is then `1 / C(r+s, r)`, so the sum bound reads `m / C(r+s, r) ≤ 1`.

## 2-colourable hypergraphs (§1.3)

`PMC.TwoColorable E` says some two-colouring of the ground set leaves no member of `E`
monochromatic — property B.

### property_b_lower
`PMC.twoColorable_of_card_lt_two_pow` — Theorem 1.3.1 (Erdős 1964).

Every `k`-uniform hypergraph with fewer than `2^(k-1)` edges is 2-colourable, i.e.
`m(k) ≥ 2^(k-1)`.

Zhao's proof: a uniformly random 2-colouring makes each edge monochromatic with
probability `2^(1-k)`, so the expected number of monochromatic edges is
`#E · 2^(1-k) < 1`. Counting form: fewer than `2 ^ #V` of the colourings are bad.

Theorem 1.3.3 (`m(k) = O(k² 2^k)`) was recorded here as "asymptotic and not a node in this
phase". The `O(·)` is the only asymptotic part, and the proof pins the constant down:
`PMC.exists_not_twoColorable_card_le` states that some `k`-uniform hypergraph on `k²` vertices
with at most `2 k² 2^k` edges is not 2-colourable, which is the theorem with `O(k² 2^k)`
replaced by an explicit bound. Statement published as a task; the route is in the file's
docstring, and the constant has slack (`1.386 k² 2^k` is what the estimates give). With
Theorem 1.3.1 below (`m k ≥ 2^{k-1}`) and Theorem 3.5.1 (`m k ≳ √(k/log k) 2^k`) this brackets
`m k`.

### ramsey_lll — Theorem 1.1.9 (Spencer 1977)

`PMC.not_ramseyProp_of_lll` (`ProbMethods/Chapter01/RamseyLLL.lean`): if
`e (C(k,2)·C(n,k-2) + 1) 2^{1-C(k,2)} ≤ 1` then `R(k,k) > n`. This is Theorem 1.1.8, the local
lemma in the random variable model (`PMC.exists_avoiding_of_lll`), applied to the uniform
random 2-colouring of `E(Kₙ)` with one bad event per `k`-subset.

Three points worth recording:

* **the coordinate type is every subset of `[n]`, not every edge.** A colouring is
  `f : Finset (Fin n) → Bool` and only the 2-element subsets are read. The extra coordinates
  are independent and no event depends on them, so they cost nothing — and `S.powersetCard 2`
  is then literally "the edges inside `S`", with `Finset.card_powersetCard` handing over
  `C(#S, 2)`. Same trick as tossing a coin for each loop in §4's `Sym2` model.
* **the dependency count needs no canonical choice.** The notes bound the number of `S'` with
  `#(S ∩ S') ≥ 2` by `C(k,2)·C(n,k-2)` — two shared vertices inside `S`, then `k-2` vertices
  anywhere. Formally `S' ↦ (T, S' \ T)` is injective for *any* 2-subset `T ⊆ S ∩ S'`, since
  `T ⊆ S'` makes `S'` recoverable as `T ∪ (S' \ T)`. So `T` can be picked by `choose` with no
  ordering of `Fin n` and no minimality.
* **`n < k` is separated off**, because the local lemma wants `0 < d` and
  `d = C(k,2)·C(n,k-2)` vanishes when `n < k-2`; there `Kₙ` has no `k`-clique at all.

Checked numerically before committing: the bound overtakes the union-bound Theorem 1.1.2
(`2 C(n,k) < 2^{C(k,2)}`) at `k = 11`, and the ratio of admissible `n` climbs to `1.42` by
`k = 25` — the `√2` that is Spencer's factor-2 improvement of the constant in
`R(k,k) > (1+o(1)) (√2/e) k 2^{k/2}`.

## List chromatic number of `K_{n,n}` (§1.4)

`PMC.CompleteBipartiteChoosable n k` says `K_{n,n}` — vertex set `Fin n ⊕ Fin n`, adjacent
exactly across the two sides — is `k`-choosable. Colours are taken in `ℕ`, which costs no
generality: only finitely many colours appear in the lists, so any colour set transports
along an injection into `ℕ`. A colouring is proper here precisely when no colour is used
on both sides.

### choosable_upper
`PMC.completeBipartiteChoosable_of_lt_two_pow` — Theorem 1.4.2.

If `n < 2^(k-1)` then `K_{n,n}` is `k`-choosable; equivalently `ch(K_{n,n}) ≤ ⌊log₂(2n)⌋ + 1`.

Zhao's proof: mark each colour `L` or `R` independently and uniformly; delete `R`-marked
colours from left lists and `L`-marked colours from right lists. A given vertex is
emptied with probability `2^(-k)`, so the union bound over `2n` vertices gives a marking
that empties nobody, and choosing from what survives never repeats a colour across sides.

### choosable_lower
`PMC.not_completeBipartiteChoosable_of_not_twoColorable` — Theorem 1.4.3.

If some `k`-uniform hypergraph with `n` edges is not 2-colourable, then `K_{n,n}` is not
`k`-choosable. View the hypergraph's vertices as colours and give the `i`-th vertex on
each side the list consisting of the `i`-th edge; a proper list colouring would 2-colour
the hypergraph.

Corollary 1.4.4 (`ch(K_{n,n}) = (1 + o(1)) log₂ n`) and Theorem 1.4.5 (Saxton–Thomason)
are asymptotic and depend on Chapter 11; not nodes in this phase.
