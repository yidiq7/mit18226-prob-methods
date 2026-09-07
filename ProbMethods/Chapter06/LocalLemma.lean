import ProbMethods.Weighted

/-!
# §6.1 — The Lovász Local Lemma

Zhao, *Probabilistic Methods in Combinatorics*, Theorem 6.1.x.

Mathlib has no local lemma, and unlike Talagrand or the container theorem this one is
fully expressible in the finite weighted framework of `ProbMethods/Weighted.lean`: events
are `Finset`s of a finite sample space, `PMC.wprob` is their probability, and the
dependency structure is a neighbour map `N : ι → Finset ι`.

Intersections of complements are written `T.inf (fun j => (A j)ᶜ)`, which is `⋂ j ∈ T, (A j)ᶜ`
and is `univ` when `T = ∅` — exactly the convention the induction needs.
-/

open Finset

namespace PMC

section LocalLemma

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- The event that none of the `A j` for `j ∈ T` occurs. -/
def noneOf (A : ι → Finset Ω) (T : Finset ι) : Finset Ω := T.inf fun j => (A j)ᶜ

@[simp] lemma noneOf_empty (A : ι → Finset Ω) : noneOf A ∅ = (univ : Finset Ω) := by
  simp [noneOf]

lemma noneOf_insert (A : ι → Finset Ω) (i : ι) (T : Finset ι) :
    noneOf A (insert i T) = (A i)ᶜ ∩ noneOf A T := by
  simp [noneOf, Finset.inf_insert]

lemma noneOf_subset (A : ι → Finset Ω) {T U : Finset ι} (h : T ⊆ U) :
    noneOf A U ⊆ noneOf A T := Finset.inf_mono h

/-- **The Lovász Local Lemma**, asymmetric form (Zhao, Theorem 6.1.x).

If each event `A i` has probability at most `x i * ∏ j ∈ N i, (1 - x j)`, and each `A i` is
independent of any family of complements drawn from outside `insert i (N i)`, then with
positive probability none of the events occurs — indeed the probability is at least
`∏ i, (1 - x i)`, which is positive because each `x i < 1`.

The independence hypothesis is the standard one, stated here as an equality of weights for
every subfamily `T` disjoint from `insert i (N i)`. That "for every subfamily" is essential
and is what mutual independence means; pairwise independence is not enough.

**Proof strategy** (the part a prover has to supply). By induction on `#T`, show

    ∀ i ∉ T,  wprob w (A i ∩ noneOf A T) ≤ x i * wprob w (noneOf A T)

Split `T` as `T₁ = T ∩ N i` and `T₂ = T \ N i`. The numerator is bounded using
independence across `T₂`, giving `wprob w (A i) * wprob w (noneOf A T₂)`; the denominator is
bounded below by `∏ j ∈ T₁, (1 - x j)` times `wprob w (noneOf A T₂)` using the inductive
hypothesis on the strictly smaller sets obtained by peeling `T₁` one element at a time.
Since `T₁ ⊆ N i`, the product `∏ j ∈ N i, (1 - x j)` in `hbound` dominates
`∏ j ∈ T₁, (1 - x j)` and the ratio collapses to `x i`.

The conclusion then follows by a second induction, on `S`, from
`wprob w (noneOf A (insert i S)) ≥ (1 - x i) * wprob w (noneOf A S)`.

Both inductions are genuinely needed, and the conditional-probability bookkeeping of the
informal proof has to be replaced by multiplicative inequalities to avoid dividing by a
quantity not yet known to be positive. -/
theorem lovasz_local_lemma (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω = 1)
    (A : ι → Finset Ω) (N : ι → Finset ι) (x : ι → ℝ)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hself : ∀ i, i ∉ N i)
    (hindep : ∀ (i : ι) (T : Finset ι), Disjoint T (insert i (N i)) →
      wprob w (A i ∩ noneOf A T) = wprob w (A i) * wprob w (noneOf A T))
    (hbound : ∀ i, wprob w (A i) ≤ x i * ∏ j ∈ N i, (1 - x j)) :
    ∏ i, (1 - x i) ≤ wprob w (noneOf A (univ : Finset ι)) := by
  sorry

end LocalLemma

end PMC
