import ProbMethods.Chapter10.Shearer
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

end Intersecting

end PMC
