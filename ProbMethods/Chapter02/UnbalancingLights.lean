import ProbMethods.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Tactic.Ring

/-!
# §2.5 — Unbalancing lights

Zhao, *Probabilistic Methods in Combinatorics*, Theorem 2.5.1.

Theorem 2.5.2 and Lemma 2.5.3 are in `ProbMethods/Chapter02/PolyCube.lean`. They were recorded
here as out of scope, because the notes' proof of 2.5.3 is a compactness argument producing an
unspecified constant `c_k`; the constant is `2^{-k}`, by a finite difference over the corners
of the cube, so both results are statable and are proved.
-/

open Finset

namespace PMC

section Unbalancing

open scoped symmDiff

/-- `⌊(m+1)/2⌋` and `⌊m/2⌋` index the same binomial coefficient in row `m`. -/
private lemma choose_half (m : ℕ) : m.choose ((m + 1) / 2) = m.choose (m / 2) := by
  rcases Nat.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
  · subst hj
    congr 1
    omega
  · subst hj
    have h1 : (2 * j + 1 + 1) / 2 = j + 1 := by omega
    have h2 : (2 * j + 1) / 2 = j := by omega
    rw [h1, h2, ← Nat.choose_symm (by omega : j + 1 ≤ 2 * j + 1)]
    congr 1
    omega

/-- Telescoping form of `t * C(n, t) = n * C(n-1, t-1)`, written with `n = m + 1` so that no
truncated subtraction appears. -/
private lemma choose_mul_two_mul_sub (m u : ℕ) :
    ((m + 1).choose (u + 1) : ℤ) * (2 * ((u : ℤ) + 1) - ((m : ℤ) + 1))
      = ((m : ℤ) + 1) * ((m.choose u : ℤ) - (m.choose (u + 1) : ℤ)) := by
  have h1 : ((m + 1) * m.choose u : ℕ) = ((m + 1).choose (u + 1) * (u + 1) : ℕ) :=
    Nat.add_one_mul_choose_eq m u
  have h2 : ((m + 1).choose (u + 1) : ℕ) = m.choose u + m.choose (u + 1) :=
    Nat.choose_succ_succ' m u
  have h1' : ((m : ℤ) + 1) * (m.choose u : ℤ)
      = ((m + 1).choose (u + 1) : ℤ) * ((u : ℤ) + 1) := by exact_mod_cast h1
  have h2' : (((m + 1).choose (u + 1) : ℕ) : ℤ)
      = (m.choose u : ℤ) + (m.choose (u + 1) : ℤ) := by exact_mod_cast h2
  calc ((m + 1).choose (u + 1) : ℤ) * (2 * ((u : ℤ) + 1) - ((m : ℤ) + 1))
      = 2 * (((m + 1).choose (u + 1) : ℤ) * ((u : ℤ) + 1))
        - ((m + 1).choose (u + 1) : ℤ) * ((m : ℤ) + 1) := by ring
    _ = 2 * (((m : ℤ) + 1) * (m.choose u : ℤ))
        - ((m.choose u : ℤ) + (m.choose (u + 1) : ℤ)) * ((m : ℤ) + 1) := by rw [← h1', h2']
    _ = ((m : ℤ) + 1) * ((m.choose u : ℤ) - (m.choose (u + 1) : ℤ)) := by ring

/-- The mean absolute deviation of a symmetric binomial, cleared of denominators:
`∑ t, C(n,t) * |2t - n| = 2 * n * C(n-1, ⌊(n-1)/2⌋)`, with `n = m + 1`. -/
private lemma sum_choose_mul_abs (m : ℕ) :
    ∑ t ∈ range (m + 2), ((m + 1).choose t : ℤ) * |2 * (t : ℤ) - ((m : ℤ) + 1)|
      = 2 * ((m : ℤ) + 1) * (m.choose (m / 2) : ℤ) := by
  have hk1 : 2 * ((m + 1) / 2) ≤ m + 1 := Nat.mul_div_le (m + 1) 2
  have hk2 : m + 1 < 2 * ((m + 1) / 2) + 2 := by omega
  have hkn : (m + 1) / 2 ≤ m + 1 := Nat.div_le_self _ _
  rw [Finset.sum_range_succ' (fun t => ((m + 1).choose t : ℤ) * |2 * (t : ℤ) - ((m : ℤ) + 1)|)]
  have hzero : ((m + 1).choose 0 : ℤ) * |2 * ((0 : ℕ) : ℤ) - ((m : ℤ) + 1)| = (m : ℤ) + 1 := by
    simp [abs_of_nonpos]
  rw [hzero]
  -- split the remaining range at ⌊(m+1)/2⌋
  have hsplit : ∑ u ∈ range (m + 1),
        ((m + 1).choose (u + 1) : ℤ) * |2 * (((u + 1 : ℕ)) : ℤ) - ((m : ℤ) + 1)|
      = (∑ u ∈ range ((m + 1) / 2),
          ((m + 1).choose (u + 1) : ℤ) * |2 * (((u + 1 : ℕ)) : ℤ) - ((m : ℤ) + 1)|)
        + ∑ u ∈ Ico ((m + 1) / 2) (m + 1),
          ((m + 1).choose (u + 1) : ℤ) * |2 * (((u + 1 : ℕ)) : ℤ) - ((m : ℤ) + 1)| := by
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le _) hkn,
      Finset.range_eq_Ico]
  rw [hsplit]
  have hpart1 : ∑ u ∈ range ((m + 1) / 2),
      ((m + 1).choose (u + 1) : ℤ) * |2 * (((u + 1 : ℕ)) : ℤ) - ((m : ℤ) + 1)|
      = ((m : ℤ) + 1) * ((m.choose ((m + 1) / 2) : ℤ) - 1) := by
    have hcong : ∀ u ∈ range ((m + 1) / 2),
        ((m + 1).choose (u + 1) : ℤ) * |2 * (((u + 1 : ℕ)) : ℤ) - ((m : ℤ) + 1)|
          = ((m : ℤ) + 1) * ((m.choose (u + 1) : ℤ) - (m.choose u : ℤ)) := by
      intro u hu
      have hu' : u < (m + 1) / 2 := mem_range.mp hu
      have habs : |2 * (((u + 1 : ℕ)) : ℤ) - ((m : ℤ) + 1)|
          = -(2 * ((u : ℤ) + 1) - ((m : ℤ) + 1)) := by
        rw [show (((u + 1 : ℕ)) : ℤ) = (u : ℤ) + 1 by push_cast; ring]
        exact abs_of_nonpos (by omega)
      rw [habs, mul_neg, choose_mul_two_mul_sub m u]
      ring
    rw [Finset.sum_congr rfl hcong, ← Finset.mul_sum,
      Finset.sum_range_sub (fun u => (m.choose u : ℤ)) ((m + 1) / 2)]
    simp
  have hpart2 : ∑ u ∈ Ico ((m + 1) / 2) (m + 1),
      ((m + 1).choose (u + 1) : ℤ) * |2 * (((u + 1 : ℕ)) : ℤ) - ((m : ℤ) + 1)|
      = ((m : ℤ) + 1) * (m.choose ((m + 1) / 2) : ℤ) := by
    have hcong : ∀ u ∈ Ico ((m + 1) / 2) (m + 1),
        ((m + 1).choose (u + 1) : ℤ) * |2 * (((u + 1 : ℕ)) : ℤ) - ((m : ℤ) + 1)|
          = ((m : ℤ) + 1) * ((m.choose u : ℤ) - (m.choose (u + 1) : ℤ)) := by
      intro u hu
      have hu' : (m + 1) / 2 ≤ u := (mem_Ico.mp hu).1
      have habs : |2 * (((u + 1 : ℕ)) : ℤ) - ((m : ℤ) + 1)|
          = 2 * ((u : ℤ) + 1) - ((m : ℤ) + 1) := by
        rw [show (((u + 1 : ℕ)) : ℤ) = (u : ℤ) + 1 by push_cast; ring]
        exact abs_of_nonneg (by omega)
      rw [habs, choose_mul_two_mul_sub m u]
    rw [Finset.sum_congr rfl hcong, ← Finset.mul_sum, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_assoc]
    rw [Finset.sum_range_sub' (fun i => (m.choose ((m + 1) / 2 + i) : ℤ)) (m + 1 - (m + 1) / 2)]
    have hend : (m + 1) / 2 + (m + 1 - (m + 1) / 2) = m + 1 := by omega
    rw [Nat.add_zero, hend, Nat.choose_eq_zero_of_lt (Nat.lt_succ_self m)]
    simp
  rw [hpart1, hpart2, choose_half m]
  ring

variable {n : ℕ}

/-- The `±1` vector whose `+1` coordinates are exactly `s`. -/
private def signOf (s : Finset (Fin n)) : Fin n → ℤ := fun j => if j ∈ s then 1 else -1

private lemma signOf_eq (s : Finset (Fin n)) (j : Fin n) : signOf s j = 1 ∨ signOf s j = -1 := by
  by_cases h : j ∈ s <;> simp [signOf, h]

private lemma sum_signOf (s : Finset (Fin n)) : ∑ j, signOf s j = 2 * (#s : ℤ) - (n : ℤ) := by
  have h1 : ∀ j : Fin n, signOf s j = 2 * (if j ∈ s then (1 : ℤ) else 0) - 1 := by
    intro j; by_cases h : j ∈ s <;> simp [signOf, h]
  simp only [h1]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp

/-- Multiplying entrywise by a `±1` row turns the sign vector of `s` into that of a symmetric
difference, so the row acts on the sign vectors by a bijection. -/
private lemma mul_signOf (a : Fin n → ℤ) (ha : ∀ j, a j = 1 ∨ a j = -1)
    (s : Finset (Fin n)) (j : Fin n) :
    a j * signOf s j = signOf (s ∆ (univ.filter fun j => a j = -1)) j := by
  have hmem : j ∈ (univ.filter fun j => a j = -1) ↔ a j = -1 := by simp
  rcases ha j with h | h
  · have hnot : j ∉ (univ.filter fun j => a j = -1) := by
      rw [hmem, h]; omega
    by_cases hs : j ∈ s <;>
      simp [signOf, h, hs, Finset.mem_symmDiff, hnot]
  · have hin : j ∈ (univ.filter fun j => a j = -1) := hmem.mpr h
    by_cases hs : j ∈ s <;>
      simp [signOf, h, hs, Finset.mem_symmDiff, hin]

private lemma sum_abs_row (a : Fin n → ℤ) (ha : ∀ j, a j = 1 ∨ a j = -1) :
    ∑ s : Finset (Fin n), |∑ j, a j * signOf s j|
      = ∑ s : Finset (Fin n), |2 * (#s : ℤ) - (n : ℤ)| := by
  classical
  set c : Finset (Fin n) := univ.filter (fun j => a j = -1) with hc
  refine Fintype.sum_equiv
    ⟨fun s => s ∆ c, fun s => s ∆ c, fun s => by simp [symmDiff_symmDiff_cancel_right],
      fun s => by simp [symmDiff_symmDiff_cancel_right]⟩ _ _ ?_
  intro s
  have h1 : ∑ j, a j * signOf s j = ∑ j, signOf (s ∆ c) j :=
    Finset.sum_congr rfl fun j _ => mul_signOf a ha s j
  rw [h1, sum_signOf]
  rfl

/-- Summed over all `2 ^ n` sign vectors, `|∑ j, y j|` totals `2 n C(n-1, ⌊(n-1)/2⌋)`. -/
private lemma sum_abs_sum_signOf (m : ℕ) :
    ∑ s : Finset (Fin (m + 1)), |2 * (#s : ℤ) - ((m + 1 : ℕ) : ℤ)|
      = 2 * ((m : ℤ) + 1) * (m.choose (m / 2) : ℤ) := by
  have hp : ∑ s ∈ (univ : Finset (Fin (m + 1))).powerset,
      |2 * ((#s : ℕ) : ℤ) - ((m + 1 : ℕ) : ℤ)|
      = ∑ t ∈ range (#(univ : Finset (Fin (m + 1))) + 1),
        (#(univ : Finset (Fin (m + 1)))).choose t • |2 * (t : ℤ) - ((m + 1 : ℕ) : ℤ)| :=
    Finset.sum_powerset_apply_card (fun t => |2 * (t : ℤ) - ((m + 1 : ℕ) : ℤ)|)
  rw [Finset.powerset_univ, Finset.card_univ, Fintype.card_fin] at hp
  rw [hp]
  simp only [nsmul_eq_mul]
  rw [show ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 by push_cast; ring] at *
  exact sum_choose_mul_abs m

end Unbalancing


/-- **Unbalancing lights** (Zhao, Theorem 2.5.1), with the constant made explicit.

Given an `n × n` array of `±1` values, some choice of row signs `x` and column signs `y`
makes `∑ i, ∑ j, a i j * x i * y j` at least `n ^ 2 * C(n-1, ⌊(n-1)/2⌋) / 2 ^ (n-1)`,
written multiplicatively to stay in `ℤ` with no division.

**The notes state this asymptotically**, as `(√(2/π) + o(1)) * n ^ (3/2)`, and reach that
form through the central limit theorem. The closed form above is the same bound before
that last step: the notes record in passing that
`E|S_n| = n * 2 ^ (1-n) * C(n-1, ⌊(n-1)/2⌋)` for `S_n` a sum of `n` independent uniform
`±1`, and summing over the `n` rows gives exactly this. Stating it this way keeps the node
in Chapter 2 instead of deferring it behind the machinery of Chapter 9, and follows the
roadmap's rule that asymptotic results are either deferred or made explicit.

Zhao's proof picks the column signs `y` uniformly at random, sets `R i = ∑ j, a i j * y j`,
and takes `x i` to be the sign of `R i`, so that the double sum becomes `∑ i, |R i|`. Each
`R i` is distributed as `S_n`, so the expectation is `n * E|S_n|` and some `y` attains it. -/
theorem exists_signs_two_pow_mul_le (n : ℕ) (a : Fin n → Fin n → ℤ)
    (ha : ∀ i j, a i j = 1 ∨ a i j = -1) :
    ∃ x y : Fin n → ℤ, (∀ i, x i = 1 ∨ x i = -1) ∧ (∀ j, y j = 1 ∨ y j = -1) ∧
      (n : ℤ) ^ 2 * ((n - 1).choose ((n - 1) / 2) : ℤ)
        ≤ (∑ i, ∑ j, a i j * x i * y j) * 2 ^ (n - 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨fun _ => 1, fun _ => 1, fun _ => Or.inl rfl, fun _ => Or.inl rfl, by simp⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set R : Finset (Fin (m + 1)) → Fin (m + 1) → ℤ :=
    fun s i => ∑ j, a i j * signOf s j with hR
  obtain ⟨s₀, -, hs₀⟩ := Finset.exists_max_image (univ : Finset (Finset (Fin (m + 1))))
    (fun s => ∑ i, |R s i|) univ_nonempty
  refine ⟨fun i => if 0 ≤ R s₀ i then 1 else -1, signOf s₀, ?_, fun j => signOf_eq s₀ j, ?_⟩
  · intro i; by_cases h : 0 ≤ R s₀ i <;> simp [h]
  -- the double sum collapses to `∑ i, |R s₀ i|`
  have hdouble : (∑ i, ∑ j, a i j * (if 0 ≤ R s₀ i then (1 : ℤ) else -1) * signOf s₀ j)
      = ∑ i, |R s₀ i| := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have hpull : ∑ j, a i j * (if 0 ≤ R s₀ i then (1 : ℤ) else -1) * signOf s₀ j
        = (if 0 ≤ R s₀ i then (1 : ℤ) else -1) * R s₀ i := by
      simp only [hR, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hpull]
    by_cases h : 0 ≤ R s₀ i
    · rw [if_pos h, one_mul, abs_of_nonneg h]
    · rw [if_neg h, abs_of_neg (not_le.mp h)]
      ring
  rw [hdouble]
  -- the total over all sign vectors
  have htotal : ∑ s : Finset (Fin (m + 1)), ∑ i, |R s i|
      = ((m : ℤ) + 1) * (2 * ((m : ℤ) + 1) * (m.choose (m / 2) : ℤ)) := by
    rw [Finset.sum_comm]
    have hrow : ∀ i : Fin (m + 1), ∑ s : Finset (Fin (m + 1)), |R s i|
        = 2 * ((m : ℤ) + 1) * (m.choose (m / 2) : ℤ) := by
      intro i
      simp only [hR]
      rw [sum_abs_row (a i) (ha i)]
      exact sum_abs_sum_signOf m
    rw [Finset.sum_congr rfl fun i _ => hrow i, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  -- the maximum is at least the mean
  have hmean : ∑ s : Finset (Fin (m + 1)), ∑ i, |R s i|
      ≤ (2 : ℤ) ^ (m + 1) * ∑ i, |R s₀ i| := by
    calc ∑ s : Finset (Fin (m + 1)), ∑ i, |R s i|
        ≤ ∑ _s : Finset (Fin (m + 1)), ∑ i, |R s₀ i| :=
          Finset.sum_le_sum fun s _ => hs₀ s (mem_univ s)
      _ = (2 : ℤ) ^ (m + 1) * ∑ i, |R s₀ i| := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin,
            nsmul_eq_mul]
          push_cast
          ring
  rw [htotal] at hmean
  have hstep : 2 * (((m : ℤ) + 1) ^ 2 * (m.choose (m / 2) : ℤ))
      ≤ 2 * ((2 : ℤ) ^ m * ∑ i, |R s₀ i|) := by
    calc 2 * (((m : ℤ) + 1) ^ 2 * (m.choose (m / 2) : ℤ))
        = ((m : ℤ) + 1) * (2 * ((m : ℤ) + 1) * (m.choose (m / 2) : ℤ)) := by ring
      _ ≤ (2 : ℤ) ^ (m + 1) * ∑ i, |R s₀ i| := hmean
      _ = 2 * ((2 : ℤ) ^ m * ∑ i, |R s₀ i|) := by rw [pow_succ]; ring
  have hcancel := le_of_mul_le_mul_left hstep (by norm_num : (0 : ℤ) < 2)
  simp only [Nat.add_sub_cancel]
  calc ((m + 1 : ℕ) : ℤ) ^ 2 * ((m.choose (m / 2) : ℕ) : ℤ)
      = ((m : ℤ) + 1) ^ 2 * (m.choose (m / 2) : ℤ) := by push_cast; ring
    _ ≤ (2 : ℤ) ^ m * ∑ i, |R s₀ i| := hcancel
    _ = (∑ i, |R s₀ i|) * 2 ^ m := by ring

end PMC
