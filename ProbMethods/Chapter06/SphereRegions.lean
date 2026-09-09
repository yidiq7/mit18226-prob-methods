import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Intervals

/-!
# §6.2 — Lemma 6.2.14, the region count of a sphere arrangement

Zhao, *Probabilistic Methods in Combinatorics*, Lemma 6.2.14: a set of `n ≥ 2` spheres in `ℝ³`
cuts `ℝ³` into at most `n³` connected components. It is the combinatorial-geometry input to
Theorem 6.2.12 (Mani-Levitska–Pach), where it bounds how many other edges an edge of the
covering hypergraph can meet.

**The geometry is hypothesized, and the statement says so.** What is formalizable here today is
the *recursion*, which is all the notes' proof actually computes:

* `f m` — the largest number of regions `m` circles can cut a sphere into. Adding a circle to
  `m` of them creates at most `2m` intersection points, so the new circle is cut into at most
  `2m` arcs and contributes at most `2m` new regions: `f (m+1) ≤ f m + 2m`, with `f 1 = 2`.
* `g m` — the largest number of regions `m` spheres can cut `ℝ³` into. A new sphere is divided
  by the others into at most `f m` pieces, each contributing one new region:
  `g (m+1) ≤ g m + f m`, with `g 1 = 2`.

`PMC.region_count_le_cube` derives `g m ≤ m³` for `m ≥ 2` from exactly those four facts and
nothing else. Establishing them for actual spheres needs a theory of arrangements that Mathlib
does not have — the "at most `2m` intersection points" step is Bézout for circles on a sphere —
so a reader should read this as the arithmetic half of 6.2.14, with the two geometric inputs
named as hypotheses rather than smuggled in.

The bound is not tight: the recursions give `g m ≤ 2m + (m-1)m(m-2)/3`, which is `m³/3`
asymptotically. `m³` is what the notes state and what Theorem 6.2.12 consumes.
-/

namespace PMC

section SphereRegions

/-- **Lemma 6.2.14**, arithmetic half: from `f 1 = 2`, `f (m+1) ≤ f m + 2m`, `g 1 = 2` and
`g (m+1) ≤ g m + f m`, the region count satisfies `g m ≤ m³` for every `m ≥ 2`.

Route: first `f m ≤ m(m-1) + 2` by induction on `m` from the two `f` facts, then
`g m ≤ g 1 + ∑_{j=1}^{m-1} f j` by induction from the two `g` facts, and finally
`2 + ∑_{j<m} (j(j-1)+2) = 2m + (m-1)m(m-2)/3 ≤ m³`, where the sum of `j(j-1)` telescopes
(`Finset.sum_range_id_mul_two` and friends, or a direct induction). -/
theorem region_count_le_cube {f g : ℕ → ℕ} (hf1 : f 1 = 2)
    (hf : ∀ m, 1 ≤ m → f (m + 1) ≤ f m + 2 * m) (hg1 : g 1 = 2)
    (hg : ∀ m, 1 ≤ m → g (m + 1) ≤ g m + f m) :
    ∀ m, 2 ≤ m → g m ≤ m ^ 3 := by
  sorry

end SphereRegions

end PMC
