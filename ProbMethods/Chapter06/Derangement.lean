import ProbMethods.Chapter06.LocalLemma
import ProbMethods.Permutation

/-!
# §6.5 — the derangement lower bound

Corollary 6.5.6: a uniform random permutation of an `n`-element set has no fixed point with
probability at least `(1 - 1/n)^n`.

This is the smallest application of the lopsided local lemma, and it shows why the lopsided
form is needed at all. The bad events `A i = {σ | σ i = i}` are *not* independent — knowing
that `σ` fixes nothing else makes `σ i = i` strictly less likely — so
`PMC.lovasz_local_lemma` does not apply. But they *are* negatively correlated
(`PMC.wprob_fix_inter_derangeOn_le`), so `PMC.lovasz_local_lemma_lopsided` does, with an
**empty** dependency neighbourhood: `N i = ∅`, `x i = 1/n`, and the conclusion
`∏ i, (1 - x i) = (1 - 1/n)^n` is immediate.

**Erratum.** The notes write "Since `P(A_i) = 1 - 1/n`, we can set `x_i = 1 - 1/n`". Both
numbers are wrong by the same slip: `P(A_i) = 1/n` and the choice is `x_i = 1/n`, which is
what makes `∏ (1 - x_i) = (1 - 1/n)^n` come out as displayed.

The exact answer `∑_{i ≤ n} (-1)^i / i!` is Remark 6.5.7 and needs inclusion–exclusion, not
the local lemma; the point here is that a two-line local-lemma argument already gives the
asymptotically optimal constant `1/e`.
-/

open Finset

namespace PMC

section Derangement

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The bad event for the derangement bound: `σ` fixes `i`. -/
abbrev fixEvent (i : α) : Finset (Equiv.Perm α) :=
  (univ : Finset (Equiv.Perm α)).filter fun σ => σ i = i

/-- Avoiding all the fixed-point events in `T` is exactly having no fixed point in `T`. -/
lemma noneOf_fixEvent (T : Finset α) :
    noneOf (fun i : α => fixEvent i) T = derangeOn T := by
  ext σ
  rw [mem_noneOf, mem_derangeOn]
  refine ⟨fun h j hj hfix => ?_, fun h j hj hmem => ?_⟩
  · exact h j hj (mem_filter.mpr ⟨mem_univ _, hfix⟩)
  · exact h j hj (mem_filter.mp hmem).2

/-- **Corollary 6.5.6 (derangement lower bound).** A uniform random permutation of an
`n`-element type has no fixed point with probability at least `(1 - 1/n)^n`.

By the lopsided local lemma with an empty dependency neighbourhood. The `n ≤ 1` cases are
separate and trivial: at `n = 1` the bound is `0`, and at `n = 0` both sides are `1`. -/
theorem wprob_derangeOn_univ_ge :
    (1 - 1 / (Fintype.card α : ℝ)) ^ Fintype.card α
      ≤ wprob (unifPerm α) (derangeOn (univ : Finset α)) := by
  rcases Nat.lt_or_ge (Fintype.card α) 2 with hsmall | hbig
  · have hcases : Fintype.card α = 0 ∨ Fintype.card α = 1 := by omega
    rcases hcases with h | h
    · -- `α` is empty: the unique permutation has no fixed point
      rw [h]
      simp only [Nat.cast_zero, div_zero, sub_zero, pow_zero]
      have hall : derangeOn (univ : Finset α) = (univ : Finset (Equiv.Perm α)) := by
        have hempty : (univ : Finset α) = ∅ := by
          rw [← Finset.card_eq_zero, card_univ, h]
        rw [derangeOn, hempty]
        simp
      rw [hall, wprob_univ, sum_unifPerm]
    · -- one point: the bound is `0`
      rw [h]
      norm_num
      exact wprob_nonneg unifPerm_nonneg _
  · -- the local lemma
    have hApos : (0 : ℝ) < Fintype.card α := by
      have : 0 < Fintype.card α := by omega
      exact_mod_cast this
    have hA1 : (1 : ℝ) < Fintype.card α := by
      have : (2 : ℕ) ≤ Fintype.card α := hbig
      have : (2 : ℝ) ≤ Fintype.card α := by exact_mod_cast this
      linarith
    have hne : Nonempty α := Fintype.card_pos_iff.mp (by omega)
    set x : α → ℝ := fun _ => 1 / (Fintype.card α : ℝ) with hxdef
    have hx0 : ∀ i, 0 ≤ x i := fun i => by rw [hxdef]; positivity
    have hx1 : ∀ i, x i < 1 := fun i => by
      rw [hxdef]
      simpa using (div_lt_one hApos).mpr hA1
    have hlop : ∀ (i : α) (T : Finset α), Disjoint T (insert i (∅ : Finset α)) →
        wprob (unifPerm α) (fixEvent i ∩ noneOf (fun j : α => fixEvent j) T)
          ≤ wprob (unifPerm α) (fixEvent i)
            * wprob (unifPerm α) (noneOf (fun j : α => fixEvent j) T) := by
      intro i T hT
      have hiT : i ∉ T := fun h => (Finset.disjoint_left.mp hT h) (mem_insert_self i ∅)
      rw [noneOf_fixEvent]
      exact wprob_fix_inter_derangeOn_le i hiT
    have hbound : ∀ i : α, wprob (unifPerm α) (fixEvent i)
        ≤ x i * ∏ j ∈ (∅ : Finset α), (1 - x j) := by
      intro i
      rw [Finset.prod_empty, mul_one, hxdef, wprob_unifPerm_apply_eq i i]
    have h := lovasz_local_lemma_lopsided (unifPerm α) unifPerm_nonneg sum_unifPerm
      (fun i : α => fixEvent i) (fun _ => (∅ : Finset α)) x hx0 hx1
      (fun i => Finset.notMem_empty i) hlop hbound
    rw [noneOf_fixEvent] at h
    calc (1 - 1 / (Fintype.card α : ℝ)) ^ Fintype.card α
        = ∏ _i : α, (1 - x _i) := by
          simp only [hxdef]
          rw [Finset.prod_const, card_univ]
      _ ≤ wprob (unifPerm α) (derangeOn (univ : Finset α)) := h

end Derangement

end PMC
