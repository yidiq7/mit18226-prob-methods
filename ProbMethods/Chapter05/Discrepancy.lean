import ProbMethods.Chapter05.Chernoff
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# §5.1 — Discrepancy

Zhao, *Probabilistic Methods in Combinatorics*, Theorem 5.1.1.

Colour the ground set `±1`; the "sum on an edge `A`" is `2 * #(S ∩ A) - #A`, where `S` is
the set of `+1` vertices. The notes' bound is `O(√(n log m))`; the explicit constant the
proof gives is `2`, which is what is stated.
-/

open Finset

namespace PMC

/-- **Low-discrepancy colourings exist** (Zhao, Theorem 5.1.1).

For any family `F` of `m ≥ 3` subsets of an `n`-element ground set there is a `±1`
colouring under which every edge's sum is at most `2 √(n log m)` in absolute value.

The notes state `O(√(n log m))`; the constant `2` is what their proof actually yields.

**`3 ≤ #F` is needed, and the notes gloss it.** The union bound gives failure at most
`2/m`, and the notes conclude "with probability greater than `1 - 2/m ≥ 0`" — but `≥ 0` does
not produce a colouring. It needs `> 0`, i.e. `m > 2`.

The proof: apply the two-sided Chernoff bound
(`PMC.card_filter_abs_sign_sum_le`) on each edge with `λ = 2 √(log m)`, lift from that
edge's coordinates to the whole ground set with `PMC.card_filter_inter`, and union bound
over the `m` edges. -/
theorem exists_low_discrepancy {V : Type*} [Fintype V] [DecidableEq V]
    (F : Finset (Finset V)) (hm : 3 ≤ #F) :
    ∃ S : Finset V, ∀ A ∈ F,
      |2 * (#(S ∩ A) : ℝ) - #A|
        ≤ 2 * Real.sqrt (Fintype.card V * Real.log (#F)) := by
  classical
  set n : ℕ := Fintype.card V with hn
  set m : ℕ := #F with hmdef
  have hm1 : (1 : ℝ) < m := by exact_mod_cast lt_of_lt_of_le (by norm_num) hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hlogpos : 0 < Real.log m := Real.log_pos hm1
  set lam : ℝ := 2 * Real.sqrt (Real.log m) with hlamdef
  have hlam : 0 < lam := by
    rw [hlamdef]
    have := Real.sqrt_pos.mpr hlogpos
    linarith
  set thr : ℝ := 2 * Real.sqrt (n * Real.log m) with hthrdef
  -- The threshold dominates the per-edge Chernoff threshold.
  have hdom : ∀ A : Finset V, lam * Real.sqrt (#A) ≤ thr := by
    intro A
    have hAle : (#A : ℝ) ≤ n := by
      rw [hn, ← card_univ]
      exact_mod_cast card_le_univ A
    rw [hlamdef, hthrdef, mul_assoc, ← Real.sqrt_mul hlogpos.le]
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by norm_num)
    rw [mul_comm (Real.log m) (#A : ℝ)]
    exact mul_le_mul_of_nonneg_right hAle hlogpos.le
  -- `exp (-lam ^ 2 / 2) = m ^ (-2)`.
  have hexp : Real.exp (-(lam ^ 2) / 2) = (m : ℝ)⁻¹ * (m : ℝ)⁻¹ := by
    have hsq : lam ^ 2 = 4 * Real.log m := by
      rw [hlamdef, mul_pow, Real.sq_sqrt hlogpos.le]
      norm_num
    rw [hsq, show -(4 * Real.log m) / 2 = -(Real.log m) + -(Real.log m) by ring,
      Real.exp_add, Real.exp_neg, Real.exp_log hmpos]
  -- Bad colourings, edge by edge.
  set bad : Finset V → Finset (Finset V) := fun A =>
    (univ : Finset V).powerset.filter
      (fun S => thr < |2 * (#(S ∩ A) : ℝ) - #A|) with hbaddef
  have hbadcard : ∀ A : Finset V, (#(bad A) : ℝ) ≤ 2 * (2 ^ n * ((m : ℝ)⁻¹ * (m : ℝ)⁻¹)) := by
    intro A
    by_cases hA : 0 < #A
    · have hlift := card_filter_inter (univ : Finset V) A (subset_univ A)
        (fun T => thr < |2 * (#T : ℝ) - #A|)
      have hsub : A.powerset.filter (fun T => thr < |2 * (#T : ℝ) - #A|)
          ⊆ A.powerset.filter (fun T => lam * Real.sqrt (#A) ≤ |2 * (#T : ℝ) - #A|) := by
        intro T hT
        rw [mem_filter] at hT ⊢
        exact ⟨hT.1, le_of_lt (lt_of_le_of_lt (hdom A) hT.2)⟩
      have hchern := card_filter_abs_sign_sum_le A hA hlam
      rw [hexp] at hchern
      have hcards : (#(A.powerset.filter fun T => thr < |2 * (#T : ℝ) - #A|) : ℝ)
          ≤ 2 * (2 ^ #A * ((m : ℝ)⁻¹ * (m : ℝ)⁻¹)) := by
        refine le_trans ?_ hchern
        exact_mod_cast card_le_card hsub
      have hsplit : #((univ : Finset V) \ A) + #A = n := by
        rw [card_sdiff_of_subset (subset_univ A), card_univ, hn]
        have : #A ≤ n := by rw [hn, ← card_univ]; exact card_le_univ A
        omega
      rw [hbaddef, hlift]
      push_cast
      calc (2 : ℝ) ^ #((univ : Finset V) \ A)
            * (#(A.powerset.filter fun T => thr < |2 * (#T : ℝ) - #A|) : ℝ)
          ≤ 2 ^ #((univ : Finset V) \ A) * (2 * (2 ^ #A * ((m : ℝ)⁻¹ * (m : ℝ)⁻¹))) := by
            exact mul_le_mul_of_nonneg_left hcards (by positivity)
        _ = 2 * (2 ^ n * ((m : ℝ)⁻¹ * (m : ℝ)⁻¹)) := by
            rw [← hsplit, pow_add]
            ring
    · -- An empty edge has sum `0`, and `thr ≥ 0`, so nothing is bad.
      have hA0 : #A = 0 := by omega
      have hempty : bad A = ∅ := by
        rw [hbaddef, Finset.eq_empty_iff_forall_notMem]
        intro S hS
        rw [mem_filter] at hS
        have hSA : #(S ∩ A) = 0 := by
          have : S ∩ A ⊆ A := inter_subset_right
          have := card_le_card this
          omega
        rw [hSA, hA0] at hS
        simp only [Nat.cast_zero, mul_zero, sub_zero, abs_zero] at hS
        have hthr0 : 0 ≤ thr := by
          rw [hthrdef]
          positivity
        linarith [hS.2]
      rw [hempty]
      simp only [card_empty, Nat.cast_zero]
      positivity
  -- Union bound.
  have hunion : (#(F.biUnion bad) : ℝ) ≤ 2 * (2 ^ n * (m : ℝ)⁻¹) := by
    calc (#(F.biUnion bad) : ℝ) ≤ ((∑ A ∈ F, #(bad A) : ℕ) : ℝ) := by
          exact_mod_cast card_biUnion_le
      _ = ∑ A ∈ F, (#(bad A) : ℝ) := by push_cast; ring
      _ ≤ ∑ _A ∈ F, 2 * (2 ^ n * ((m : ℝ)⁻¹ * (m : ℝ)⁻¹)) :=
          Finset.sum_le_sum fun A _ => hbadcard A
      _ = 2 * (2 ^ n * (m : ℝ)⁻¹) := by
          rw [Finset.sum_const, hmdef, nsmul_eq_mul]
          field_simp
  have hlt : (#(F.biUnion bad) : ℝ) < ((2 : ℝ) ^ n) := by
    have hm3 : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hinv : 2 * (m : ℝ)⁻¹ < 1 := by
      rw [show (2 : ℝ) * (m : ℝ)⁻¹ = 2 / m by field_simp, div_lt_one hmpos]
      linarith
    have hpow : (0 : ℝ) < 2 ^ n := by positivity
    have h2 : 2 * (2 ^ n * (m : ℝ)⁻¹) < (2 : ℝ) ^ n := by
      calc 2 * ((2 : ℝ) ^ n * (m : ℝ)⁻¹) = (2 * (m : ℝ)⁻¹) * 2 ^ n := by ring
        _ < 1 * 2 ^ n := mul_lt_mul_of_pos_right hinv hpow
        _ = (2 : ℝ) ^ n := one_mul _
    linarith [hunion]
  -- Some colouring avoids every bad set.
  have hcardpow : (#((univ : Finset V).powerset) : ℝ) = (2 : ℝ) ^ n := by
    rw [card_powerset, card_univ, hn]
    push_cast
    ring
  have hstrict : #(F.biUnion bad) < #((univ : Finset V).powerset) := by
    have := hlt
    rw [← hcardpow] at this
    exact_mod_cast this
  obtain ⟨S, -, hSbad⟩ := exists_mem_notMem_of_card_lt_card hstrict
  refine ⟨S, fun A hA => ?_⟩
  by_contra hcon
  rw [not_le] at hcon
  exact hSbad (mem_biUnion.mpr ⟨A, hA, by
    rw [hbaddef, mem_filter]
    exact ⟨mem_powerset.mpr (subset_univ S), hcon⟩⟩)

end PMC
