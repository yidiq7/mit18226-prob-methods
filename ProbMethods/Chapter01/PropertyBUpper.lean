import ProbMethods.Chapter01.PropertyB

/-!
# §1.3 — Theorem 1.3.3, the upper bound `m(k) = O(k² 2^k)`

Zhao, *Probabilistic Methods in Combinatorics*, Theorem 1.3.3 (Erdős 1964): there is a
`k`-uniform hypergraph with `O(k² 2^k)` edges that is not 2-colourable — so `m k = O(k² 2^k)`,
where `m k` is the least number of edges of a non-2-colourable `k`-uniform hypergraph.
Together with `PMC.twoColorable_of_card_lt_two_pow` (Theorem 1.3.1, `m k ≥ 2^{k-1}`) and
`PMC.twoColorable_of_card_le` (Theorem 3.5.1, `m k ≳ √(k/log k) 2^k`) this brackets `m k`.

**Stated with an explicit constant**, as the roadmap requires: `2 k² 2^k` edges suffice. The
notes' `O(·)` hides a constant that the proof below pins down, and the arithmetic has slack —
`1.39 k² 2^k` is what the estimates give, so `2 k² 2^k` is comfortable.

## The route

Vertices `[k²]`; choose `m = 2 k² 2^k` edges independently and uniformly among all `k`-subsets,
and show some choice is not 2-colourable. Fix a colouring `c`, and let its larger colour class
have `s ≥ k²/2` vertices.

* **A random `k`-set is monochromatic with probability at least `2^{-k-1}`.** It suffices to
  land inside the larger class:

      C(s,k)/C(k²,k) ≥ ∏_{i<k} (k²/2 - i)/(k² - i) ≥ 2^{-k} ∏_{i<k} (1 - i/(k² - k))
                     ≥ 2^{-k} (1 - k(k-1)/(2(k² - k))) = 2^{-k-1},

  the last equality because `k(k-1)/(2(k²-k)) = 1/2` exactly at `k²` vertices. Only
  `∏(1 - xᵢ) ≥ 1 - ∑ xᵢ` is used, which is Weierstrass and holds in `ℕ`-free form.
* **Union bound over colourings.** For a fixed `c`, the probability that no chosen edge is
  monochromatic is at most `(1 - 2^{-k-1})^m ≤ exp(-m 2^{-k-1})`, and there are `2^{k²}`
  colourings, so the failure probability is at most `exp(k² log 2 - m 2^{-k-1}) < 1` as soon as
  `m > k² log 2 · 2^{k+1}`. At `m = 2 k² 2^k` this needs `2 > 2 log 2 = 1.386`.
* **Duplicates are harmless.** The chosen `k`-sets may coincide; the event "no chosen edge is
  monochromatic under `c`" depends only on the *set* `E` of chosen edges, so the surviving `E`
  is not 2-colourable and has `#E ≤ m`. That is why the conclusion is `≤`, not `=`.

The sample space is the `m`-fold product of the `k`-subsets of `[k²]`, i.e. a `unifProd` on
`Fin m → Finset (Fin (k*k))` restricted to `powersetCard k`; the union bound is
`PMC.wprob_biUnion_le`. Nothing here needs the local lemma or a second moment.
-/

open Finset

namespace PMC

section PropertyBUpper

/-- **Theorem 1.3.3** (Erdős 1964) with an explicit constant: for every `k ≥ 2` there is a
`k`-uniform hypergraph on `k²` vertices with at most `2 k² 2^k` edges that is not
2-colourable. Hence `m k ≤ 2 k² 2^k = O(k² 2^k)`. -/
theorem exists_not_twoColorable_card_le {k : ℕ} (hk : 2 ≤ k) :
    ∃ E : Finset (Finset (Fin (k * k))),
      (∀ e ∈ E, #e = k) ∧ #E ≤ 2 * (k * k) * 2 ^ k ∧ ¬ TwoColorable E := by
  sorry

end PropertyBUpper

end PMC
