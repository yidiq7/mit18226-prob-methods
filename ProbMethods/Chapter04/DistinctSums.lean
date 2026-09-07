import ProbMethods.Weighted
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Floor.Defs

/-!
# §4.6 — Erdős' distinct subset sums problem

Zhao, *Probabilistic Methods in Combinatorics*, §4.6.

If `a₁, …, aₙ` are positive integers whose `2 ^ n` subset sums are all distinct, how small
can the largest of them be? Powers of two give `2 ^ (n-1)`; the second-moment method shows
you cannot do better than `2 ^ n / √n` up to a constant.

The statement here is finite and explicit — no `o(1)`, no asymptotics:

`3 · 2 ^ n ≤ 8 √n · M + 4` for any upper bound `M` on the `aᵢ`.

Rearranged, `M ≥ (3 · 2 ^ n - 4) / (8 √n)`.

The proof is the book's. Take a uniformly random subset; the sum has mean `(∑ aᵢ)/2` and
variance `(∑ aᵢ²)/4 ≤ n M² / 4` (`PMC.wvar_bweight_linear`), so by Chebyshev at
`t = √n M` at least three quarters of the `2 ^ n` subsets have their sum within `t` of the
mean. Distinctness makes those sums distinct integers inside an interval of length `2t`, of
which there are at most `2t + 1`.
-/

open Finset

namespace PMC

section DistinctSums

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Under the uniform weight every subset has weight `2 ^ (-n)`. -/
lemma bweight_half (S : Finset α) :
    bweight (1 / 2 : ℝ) S = (1 / 2) ^ Fintype.card α := by
  have hle : #S ≤ Fintype.card α := by
    rw [← card_univ]
    exact card_le_card (subset_univ S)
  rw [bweight, show (1 : ℝ) - 1 / 2 = 1 / 2 from by norm_num, ← pow_add,
    Nat.add_sub_cancel' hle]

lemma wprob_bweight_half (A : Finset (Finset α)) :
    wprob (bweight (1 / 2 : ℝ)) A = #A * (1 / 2) ^ Fintype.card α := by
  rw [wprob, Finset.sum_congr rfl fun S _ => bweight_half S, Finset.sum_const, nsmul_eq_mul]

/-- **Counting integers in an interval.** A family carrying distinct integer values, all
inside `[lo, hi]`, has at most `hi - lo + 1` members. -/
lemma card_le_of_inj_bounded {A : Finset (Finset α)} (hA : A.Nonempty) (f : Finset α → ℕ)
    (hinj : ∀ S ∈ A, ∀ T ∈ A, f S = f T → S = T) {lo hi : ℝ}
    (hb : ∀ S ∈ A, lo ≤ (f S : ℝ) ∧ (f S : ℝ) ≤ hi) :
    (#A : ℝ) ≤ hi - lo + 1 := by
  classical
  obtain ⟨S₀, hS₀⟩ := hA
  have hhi0 : (0 : ℝ) ≤ hi := le_trans (Nat.cast_nonneg _) (hb S₀ hS₀).2
  have hcard : #(A.image f) = #A :=
    Finset.card_image_of_injOn fun S hS T hT h => hinj S hS T hT h
  have hsub : A.image f ⊆ Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊ := by
    intro m hm
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hm
    rw [Finset.mem_Icc]
    exact ⟨Nat.ceil_le.mpr (hb S hS).1, Nat.le_floor (hb S hS).2⟩
  have hord : ⌈lo⌉₊ ≤ ⌊hi⌋₊ := by
    have := hsub (Finset.mem_image_of_mem f hS₀)
    rw [Finset.mem_Icc] at this
    exact le_trans this.1 this.2
  have hnat : #A ≤ ⌊hi⌋₊ + 1 - ⌈lo⌉₊ := by
    have h := Finset.card_le_card hsub
    rwa [hcard, Nat.card_Icc] at h
  have hcast : ((⌊hi⌋₊ + 1 - ⌈lo⌉₊ : ℕ) : ℝ) = (⌊hi⌋₊ : ℝ) + 1 - (⌈lo⌉₊ : ℝ) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have h1 : (#A : ℝ) ≤ (⌊hi⌋₊ : ℝ) + 1 - (⌈lo⌉₊ : ℝ) := by
    rw [← hcast]
    exact_mod_cast hnat
  have h2 : (⌊hi⌋₊ : ℝ) ≤ hi := Nat.floor_le hhi0
  have h3 : lo ≤ (⌈lo⌉₊ : ℝ) := Nat.le_ceil lo
  linarith

/-- **Erdős' distinct subset sums bound** (Zhao, §4.6).

If every subset sum of `a` is distinct and `a i ≤ M` for all `i`, then
`3 · 2 ^ n ≤ 8 √n M + 4` — so the largest element is at least `(3 · 2 ^ n - 4) / (8 √n)`,
which is `2 ^ n / √n` up to a constant. -/
theorem three_mul_two_pow_le_of_distinct_sums (a : α → ℕ) (M : ℕ)
    (hn : 1 ≤ Fintype.card α) (hM : 1 ≤ M) (hle : ∀ i, a i ≤ M)
    (hdist : ∀ S T : Finset α, ∑ i ∈ S, a i = ∑ i ∈ T, a i → S = T) :
    3 * 2 ^ Fintype.card α
      ≤ 8 * Real.sqrt (Fintype.card α) * M + 4 := by
  classical
  set n := Fintype.card α with hndef
  set w : Finset α → ℝ := bweight (1 / 2 : ℝ) with hwdef
  set X : Finset α → ℝ := fun S => ∑ i ∈ S, (a i : ℝ) with hXdef
  have hw : ∀ S, 0 ≤ w S := fun S => bweight_nonneg (by norm_num) (by norm_num) S
  have hsumw : ∑ S : Finset α, w S = 1 := by
    have h := sum_bweight (α := α) (1 / 2 : ℝ)
    rwa [Finset.powerset_univ] at h
  -- the variance, and the Chebyshev radius
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  set t : ℝ := Real.sqrt n * M with htdef
  have htpos : 0 < t := by
    rw [htdef]
    exact mul_pos (Real.sqrt_pos.mpr hnR) hMR
  have htsq : t ^ 2 = n * M ^ 2 := by
    rw [htdef, mul_pow, Real.sq_sqrt (le_of_lt hnR)]
  have hvar : wvar w X = 1 / 4 * ∑ i, (a i : ℝ) ^ 2 := by
    rw [hwdef, hXdef, wvar_bweight_linear]
    ring
  have hvarle : wvar w X ≤ 1 / 4 * t ^ 2 := by
    rw [hvar, htsq]
    have hbnd : ∑ i, (a i : ℝ) ^ 2 ≤ (n : ℝ) * M ^ 2 := by
      calc ∑ i, (a i : ℝ) ^ 2 ≤ ∑ _i : α, (M : ℝ) ^ 2 := by
            refine Finset.sum_le_sum fun i _ => ?_
            have : (a i : ℝ) ≤ M := by exact_mod_cast hle i
            exact pow_le_pow_left₀ (Nat.cast_nonneg _) this 2
        _ = (n : ℝ) * M ^ 2 := by rw [Finset.sum_const, card_univ, nsmul_eq_mul, hndef]
    linarith
  -- Chebyshev: at least three quarters of the subsets are within `t` of the mean
  set A : Finset (Finset α) := univ.filter fun S => |X S - wmean w X| < t with hAdef
  have hcheb := wchebyshev' w X hw htpos
  rw [hsumw, one_mul] at hcheb
  have hprobA : wprob w A = #A * (1 / 2) ^ n := by
    rw [hwdef, hAdef, wprob_bweight_half, hndef]
  have hAsum : ∑ S ∈ A, w S = #A * (1 / 2 : ℝ) ^ n := by
    rw [← hprobA, wprob]
  rw [hAsum] at hcheb
  have hlow : 3 / 4 * 2 ^ n ≤ (#A : ℝ) := by
    have hts : (0 : ℝ) < t ^ 2 := by positivity
    have h1 : 3 / 4 * t ^ 2 ≤ (#A : ℝ) * (1 / 2) ^ n * t ^ 2 := by linarith
    have h2 : 3 / 4 ≤ (#A : ℝ) * (1 / 2) ^ n := by
      rcases le_total (3 / 4 : ℝ) ((#A : ℝ) * (1 / 2) ^ n) with h | h
      · exact h
      · nlinarith [h1, hts, mul_le_mul_of_nonneg_right h (le_of_lt hts)]
    have h3 : ((1 : ℝ) / 2) ^ n * 2 ^ n = 1 := by
      rw [div_pow, one_pow]
      field_simp
    have h4 := mul_le_mul_of_nonneg_right h2
      (le_of_lt (pow_pos (by norm_num : (0 : ℝ) < 2) n))
    rw [mul_assoc, h3, mul_one] at h4
    exact h4
  -- distinctness turns the count into a count of integers in an interval of length `2t`
  have hApos : (0 : ℝ) < #A := lt_of_lt_of_le (by positivity) hlow
  have hAne : A.Nonempty := by
    rw [← Finset.card_pos]
    exact_mod_cast hApos
  have hbnd : ∀ S ∈ A, wmean w X - t ≤ ((∑ i ∈ S, a i : ℕ) : ℝ)
      ∧ ((∑ i ∈ S, a i : ℕ) : ℝ) ≤ wmean w X + t := by
    intro S hS
    rw [hAdef, mem_filter] at hS
    have hcast : ((∑ i ∈ S, a i : ℕ) : ℝ) = X S := by
      rw [hXdef]
      push_cast
      rfl
    rw [hcast]
    have := abs_lt.mp hS.2
    constructor <;> linarith [this.1, this.2]
  have hupper : (#A : ℝ) ≤ 2 * t + 1 := by
    have h := card_le_of_inj_bounded hAne (fun S => ∑ i ∈ S, a i)
      (fun S _ T _ h => hdist S T h) hbnd
    have : wmean w X + t - (wmean w X - t) + 1 = 2 * t + 1 := by ring
    linarith [h]
  -- assemble
  have : 3 / 4 * 2 ^ n ≤ 2 * t + 1 := le_trans hlow hupper
  rw [htdef] at this
  linarith
