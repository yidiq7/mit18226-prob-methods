import ProbMethods.Chapter10.LoomisWhitney
import Mathlib.Combinatorics.SetFamily.Intersecting

/-!
# §10.4 — Ingredients for Theorem 10.4.9 (triangle-intersecting families)

Zhao, *Probabilistic Methods in Combinatorics*, Theorem 10.4.9 (Chung, Graham, Frankl and
Shearer 1986): every triangle-intersecting family of graphs on `n` labelled vertices has
size `< 2 ^ (C(n,2) - 2)`.

The notes' proof combines Corollary 10.4.7 — which is `PMC.card_pow_le_prod_card_projSet`,
already proved — with two facts that have nothing to do with entropy. This file supplies
those two, stated over an abstract ground set so neither mentions graphs:

* `PMC.two_mul_card_traceOn_le` — if every two members of a family meet *inside* `A`, then
  the family's trace on `A` has at most `2 ^ (#A - 1)` members. Mathlib's
  `Set.Intersecting.card_le` does the work; the content is that "meet inside `A`" is exactly
  what makes the traces pairwise non-disjoint.
* `PMC.exists_pair_same_side` — the pigeonhole step: any three-element set has two elements
  on the same side of a two-part split, so every triangle has an edge inside `S` or inside
  its complement.

The trace is recorded in `Finset ↥A` rather than `Finset α`. That is the whole reason the
bound comes out relative to `#A` instead of the size of the whole ground set, which would
be useless here.
-/

open Finset

namespace PMC

section Intersecting

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The trace of `F` on `A`, recorded as a family of subsets of `A` itself. -/
def traceOn (A : Finset α) (F : Finset (Finset α)) : Finset (Finset ↥A) :=
  F.image fun G => G.subtype (· ∈ A)

/-- **A family whose members pairwise meet inside `A` has trace at most half of `A`'s
powerset.** -/
theorem two_mul_card_traceOn_le (A : Finset α) (F : Finset (Finset α))
    (hF : ∀ G ∈ F, ∀ G' ∈ F, (G ∩ G' ∩ A).Nonempty) :
    2 * #(traceOn A F) ≤ 2 ^ #A := by
  classical
  have hint : ((traceOn A F : Finset (Finset ↥A)) : Set (Finset ↥A)).Intersecting := by
    intro u hu v hv hdisj
    simp only [Finset.coe_image, Set.mem_image, mem_coe, traceOn, Finset.mem_image] at hu hv
    obtain ⟨G, hG, rfl⟩ := hu
    obtain ⟨G', hG', rfl⟩ := hv
    obtain ⟨y, hy⟩ := hF G hG G' hG'
    rw [mem_inter, mem_inter] at hy
    have h1 : (⟨y, hy.2⟩ : ↥A) ∈ G.subtype (· ∈ A) := by
      rw [Finset.mem_subtype]
      exact hy.1.1
    have h2 : (⟨y, hy.2⟩ : ↥A) ∈ G'.subtype (· ∈ A) := by
      rw [Finset.mem_subtype]
      exact hy.1.2
    exact Finset.disjoint_left.mp hdisj h1 h2
  have h := hint.card_le
  rwa [Fintype.card_finset, Fintype.card_coe] at h

/-- **Pigeonhole: three elements cannot avoid sharing a side of a two-part split.**

For a set `t` with more than two elements and any `S`, two distinct members of `t` lie both
inside `S` or both outside it. Applied to a triangle, this is the notes' observation that
every triangle has an edge in `A_S = binom(S,2) ∪ binom(Sᶜ,2)`. -/
theorem exists_pair_same_side {t : Finset α} (ht : 2 < #t) (S : Finset α) :
    ∃ x ∈ t, ∃ y ∈ t, x ≠ y ∧ ((x ∈ S ∧ y ∈ S) ∨ (x ∉ S ∧ y ∉ S)) := by
  classical
  have hsplit : #(t.filter (· ∈ S)) + #(t.filter (fun x => x ∉ S)) = #t :=
    Finset.card_filter_add_card_filter_not (s := t) (· ∈ S)
  have hbig : 1 < #(t.filter (· ∈ S)) ∨ 1 < #(t.filter (fun x => x ∉ S)) := by
    by_contra hcon
    push_neg at hcon
    omega
  rcases hbig with hb | hb
  · obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hb
    rw [mem_filter] at hx hy
    exact ⟨x, hx.1, y, hy.1, hxy, Or.inl ⟨hx.2, hy.2⟩⟩
  · obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hb
    rw [mem_filter] at hx hy
    exact ⟨x, hx.1, y, hy.1, hxy, Or.inr ⟨hx.2, hy.2⟩⟩

/-- The subtype view is injective on families of subsets of `A`, so the two ways of writing
a trace — inside `A` or intersected with `A` — have the same cardinality. -/
lemma card_image_inter_eq_card_traceOn (A : Finset α) (F : Finset (Finset α)) :
    #(F.image fun G => G ∩ A) = #(traceOn A F) := by
  classical
  have hσ : traceOn A F = (F.image fun G => G ∩ A).image fun H => H.subtype (· ∈ A) := by
    rw [traceOn, Finset.image_image]
    refine Finset.image_congr fun G _ => ?_
    ext x
    simp [Finset.mem_subtype]
  rw [hσ]
  refine (Finset.card_image_of_injOn ?_).symm
  intro H hH H' hH' heq
  simp only [mem_coe, Finset.mem_image] at hH hH'
  obtain ⟨G, -, rfl⟩ := hH
  obtain ⟨G', -, rfl⟩ := hH'
  ext x
  by_cases hxA : x ∈ A
  · simpa [Finset.mem_subtype] using Finset.ext_iff.mp heq ⟨x, hxA⟩
  · simp [mem_inter, hxA]

/-- `PMC.two_mul_card_traceOn_le` with the trace written as `G ∩ A`, which is the form the
counting corollary produces. -/
theorem two_mul_card_image_inter_le (A : Finset α) (F : Finset (Finset α))
    (hF : ∀ G ∈ F, ∀ G' ∈ F, (G ∩ G' ∩ A).Nonempty) :
    2 * #(F.image fun G => G ∩ A) ≤ 2 ^ #A := by
  rw [card_image_inter_eq_card_traceOn]
  exact two_mul_card_traceOn_le A F hF

end Intersecting

/-! ### Corollary 10.4.7 — Shearer's counting form for *set families*

`PMC.card_pow_le_prod_card_projSet` is stated for families of functions `ι → β`, because
that is what `PMC.tupleEntropy` is about. The notes state Corollary 10.4.7 for a family of
*subsets*, which is what the applications use. The bridge is the indicator encoding: a
subset of `X` is a Boolean tuple, and a mask supported on `S` records exactly the trace on
`S`.
-/

section SetFamily

variable {X : Type*} [Fintype X] [LinearOrder X]

/-- Indicator encoding of a subset as a Boolean tuple. -/
def indic (G : Finset X) : X → Bool := fun x => decide (x ∈ G)

lemma indic_injective : Function.Injective (indic (X := X)) := by
  intro G G' h
  ext x
  have hx := congrFun h x
  simpa [indic] using hx

/-- **Corollary 10.4.7.** For a family `F` of subsets of `X` and index sets `A j` covering
every element at least `k` times, `#F ^ k ≤ ∏ #(F restricted to A j)`. -/
theorem card_pow_le_prod_card_image_inter (F : Finset (Finset X)) (hF : F.Nonempty)
    {κ : Type*} [DecidableEq κ] (J : Finset κ) (A : κ → Finset X) (k : ℕ)
    (hcov : ∀ x : X, k ≤ #(J.filter fun j => x ∈ A j)) :
    (#F : ℝ) ^ k ≤ ∏ j ∈ J, (#(F.image fun G => G ∩ A j) : ℝ) := by
  classical
  have hcardF : #(F.image indic) = #F :=
    Finset.card_image_of_injective F indic_injective
  have htrace : ∀ S : Finset X,
      #(projSet S (F.image indic)) = #(F.image fun G => G ∩ S) := by
    intro S
    have hψ : projSet S (F.image indic)
        = (F.image fun G => G ∩ S).image
            (fun H => fun i => if i ∈ S then some (decide (i ∈ H)) else none) := by
      rw [projSet, Finset.image_image, Finset.image_image]
      refine Finset.image_congr fun G _ => ?_
      funext i
      by_cases hi : i ∈ S <;> simp [indic, hi]
    rw [hψ]
    refine Finset.card_image_of_injOn ?_
    intro H hH H' hH' heq
    simp only [mem_coe, Finset.mem_image] at hH hH'
    obtain ⟨G, -, rfl⟩ := hH
    obtain ⟨G', -, rfl⟩ := hH'
    ext i
    by_cases hi : i ∈ S
    · have hfi := congrFun heq i
      simp only [if_pos hi, Option.some.injEq, decide_eq_decide] at hfi
      simpa [mem_inter, hi] using hfi
    · simp [mem_inter, hi]
  have h := card_pow_le_prod_card_projSet (F.image indic) (hF.image _) J A k hcov
  rw [hcardF] at h
  exact h.trans (le_of_eq (Finset.prod_congr rfl fun j _ => by rw [htrace (A j)]))

/-- **The container-style bound: intersecting traces halve every factor.**

If every trace `F|_{A j}` is an intersecting family, each factor of Corollary 10.4.7 is at
most half of that block's powerset. This is the whole non-arithmetic content of
Theorem 10.4.9 — what remains there is counting `A_S`, its size, and the covering
multiplicity. -/
theorem card_pow_le_prod_of_traces_intersecting (F : Finset (Finset X)) (hF : F.Nonempty)
    {κ : Type*} [DecidableEq κ] (J : Finset κ) (A : κ → Finset X) (k : ℕ)
    (hcov : ∀ x : X, k ≤ #(J.filter fun j => x ∈ A j))
    (hint : ∀ j ∈ J, ∀ G ∈ F, ∀ G' ∈ F, (G ∩ G' ∩ A j).Nonempty) :
    (#F : ℝ) ^ k ≤ ∏ j ∈ J, (2 : ℝ) ^ #(A j) / 2 := by
  classical
  refine (card_pow_le_prod_card_image_inter F hF J A k hcov).trans ?_
  refine Finset.prod_le_prod (fun j _ => Nat.cast_nonneg _) fun j hj => ?_
  have h := two_mul_card_image_inter_le (A j) F fun G hG G' hG' => hint j hj G hG G' hG'
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  calc (#(F.image fun G => G ∩ A j) : ℝ) * 2
      = ((2 * #(F.image fun G => G ∩ A j) : ℕ) : ℝ) := by push_cast; ring
    _ ≤ ((2 ^ #(A j) : ℕ) : ℝ) := by exact_mod_cast h
    _ = (2 : ℝ) ^ #(A j) := by push_cast; ring

end SetFamily

end PMC
