import ProbMethods.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Prime.Infinite

/-!
# §2.2 — Large sum-free subsets

Zhao, *Probabilistic Methods in Combinatorics*, Theorem 2.2.1.

Remark 2.2.2's sharpenings — Alon–Kleitman's `(n + 1) / 3`, Bourgain's `(n + 2) / 3`, and
the Eberhard–Green–Manners upper bound — are not nodes: the first two are refinements of
the same argument that the notes only sketch, and the last is asymptotic.
-/

open Finset

namespace PMC

section MiddleThird

variable {p : ℕ} [NeZero p]

/-- The *middle third* of `ZMod p`: the residues whose representative lies in
`(p / 3, 2 * p / 3]`.

Taking the middle third of **any** modulus keeps it sum-free — the interval is short
enough that a sum either overshoots `2 * p / 3` or wraps below `p / 3 + 1`. That is why
this proof needs only `Nat.exists_infinite_primes` and not Dirichlet's theorem on primes
in arithmetic progressions. -/
private def midThird (p : ℕ) [NeZero p] : Finset (ZMod p) :=
  {x ∈ (univ : Finset (ZMod p)) | p / 3 + 1 ≤ x.val ∧ x.val ≤ 2 * p / 3}

private lemma mem_midThird {x : ZMod p} :
    x ∈ midThird p ↔ p / 3 + 1 ≤ x.val ∧ x.val ≤ 2 * p / 3 := by
  simp [midThird]

private lemma zero_notMem_midThird : (0 : ZMod p) ∉ midThird p := by
  rw [mem_midThird, ZMod.val_zero]
  omega

/-- The middle third is sum-free in `ZMod p`. -/
private lemma add_notMem_midThird {x y : ZMod p} (hx : x ∈ midThird p)
    (hy : y ∈ midThird p) : x + y ∉ midThird p := by
  rw [mem_midThird] at hx hy
  rw [mem_midThird, ZMod.val_add]
  have hxp := ZMod.val_lt x
  have hyp := ZMod.val_lt y
  rcases Nat.lt_or_ge (x.val + y.val) p with hlt | hge
  · -- No wrap: the sum overshoots the top of the interval.
    rw [Nat.mod_eq_of_lt hlt]
    omega
  · -- Wrapped: the sum lands below the bottom of the interval.
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
    omega

private lemma card_midThird : #(midThird p) = 2 * p / 3 - p / 3 := by
  have hp1 : 1 ≤ p := Nat.one_le_iff_ne_zero.2 (NeZero.ne p)
  have hcard : #(Finset.Icc (p / 3 + 1) (2 * p / 3)) = 2 * p / 3 - p / 3 := by
    rw [Nat.card_Icc]; omega
  rw [← hcard]
  refine Finset.card_bij (fun x _ => x.val) ?_ ?_ ?_
  · intro x hx
    rw [mem_midThird] at hx
    exact Finset.mem_Icc.2 hx
  · intro x _ y _ hxy
    exact ZMod.val_injective p hxy
  · intro i hi
    rw [Finset.mem_Icc] at hi
    have hip : i < p := by omega
    exact ⟨(i : ZMod p), by rw [mem_midThird, ZMod.val_natCast_of_lt hip]; exact hi,
      by rw [ZMod.val_natCast_of_lt hip]⟩

/-- The middle third is large: it covers at least a third of the nonzero residues. -/
private lemma sub_one_le_three_mul_card_midThird : p - 1 ≤ 3 * #(midThird p) := by
  rw [card_midThird]
  have hr : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
  obtain hr | hr | hr := hr <;> omega

/-- Multiplication by a nonzero `a` permutes `ZMod p`, so exactly `#(midThird p)` values
of `θ` send `a` into the middle third. -/
private lemma card_filter_mul_mem [Fact p.Prime] {a : ZMod p} (ha : a ≠ 0) :
    #{θ ∈ (univ : Finset (ZMod p)) | a * θ ∈ midThird p} = #(midThird p) := by
  have himg : {θ ∈ (univ : Finset (ZMod p)) | a * θ ∈ midThird p}
      = (midThird p).image (fun x => a⁻¹ * x) := by
    ext θ
    simp only [mem_filter, mem_univ, true_and, mem_image]
    refine ⟨fun hθ => ⟨a * θ, hθ, by rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]⟩, ?_⟩
    rintro ⟨x, hx, rfl⟩
    rwa [← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  rw [himg, card_image_of_injective _ (mul_right_injective₀ (inv_ne_zero ha))]

/-- Dropping `θ = 0` from the index set changes nothing: `a * 0 = 0` is never in the
middle third. -/
private lemma filter_erase_zero (a : ZMod p) :
    {θ ∈ (univ : Finset (ZMod p)).erase 0 | a * θ ∈ midThird p}
      = {θ ∈ (univ : Finset (ZMod p)) | a * θ ∈ midThird p} := by
  ext θ
  simp only [mem_filter, mem_erase, mem_univ, and_true, true_and]
  refine ⟨fun h => h.2, fun h => ⟨fun h0 => ?_, h⟩⟩
  rw [h0, mul_zero] at h
  exact zero_notMem_midThird h

end MiddleThird

/-- **Large sum-free subsets** (Zhao, Theorem 2.2.1; Erdős 1965).

Every set of `n` nonzero integers contains a sum-free subset of size at least `n / 3`,
stated as `#A ≤ 3 * #B` to keep the claim in `ℕ` and free of division.

The book's proof averages over a *continuum*: it draws `θ` uniformly from `[0, 1]`, sets
`A_θ = {a ∈ A : {aθ} ∈ (1/3, 2/3)}` — sum-free because `(1/3, 2/3)` is sum-free in `ℝ/ℤ` —
and computes `E|A_θ| = n/3`. That route needs Lebesgue measure and is not the one to take
here; `roadmap/linearity.md` gives the discrete mod-`p` argument instead, which is a
counting proof of the same statement. -/
theorem exists_sumFree_subset (A : Finset ℤ) (h0 : (0 : ℤ) ∉ A) :
    ∃ B ⊆ A, SumFree B ∧ #A ≤ 3 * #B := by
  -- Any prime past every `|a|` will do; see `PMC.midThird`.
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (A.sup (fun a => a.natAbs) + 1)
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.pos.ne'⟩
  have hp2 : 2 ≤ p := hp.two_le
  -- Each element of `A` is a nonzero residue: it is nonzero and smaller than `p`.
  have hane : ∀ a ∈ A, ((a : ZMod p) ≠ 0) := by
    intro a ha hzero
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hzero
    have hne : a ≠ 0 := fun hc => h0 (hc ▸ ha)
    have hle : (p : ℤ) ≤ |a| := Int.le_of_dvd (abs_pos.2 hne) ((dvd_abs _ _).2 hzero)
    rw [Int.abs_eq_natAbs] at hle
    have h4 : p ≤ a.natAbs := by exact_mod_cast hle
    have h5 : a.natAbs ≤ A.sup (fun x => x.natAbs) := Finset.le_sup ha
    omega
  -- Double count pairs `(θ, a)` with `a * θ` in the middle third.
  have hdouble : ∑ θ ∈ (univ : Finset (ZMod p)).erase 0,
      #{a ∈ A | ((Int.cast a : ZMod p) * θ) ∈ midThird p} = #A * #(midThird p) := by
    calc ∑ θ ∈ (univ : Finset (ZMod p)).erase 0,
          #{a ∈ A | ((Int.cast a : ZMod p) * θ) ∈ midThird p}
        = ∑ θ ∈ (univ : Finset (ZMod p)).erase 0, ∑ a ∈ A,
            (if ((Int.cast a : ZMod p) * θ) ∈ midThird p then 1 else 0) :=
          sum_congr rfl fun θ _ => card_filter _ A
      _ = ∑ a ∈ A, ∑ θ ∈ (univ : Finset (ZMod p)).erase 0,
            (if ((Int.cast a : ZMod p) * θ) ∈ midThird p then 1 else 0) := sum_comm
      _ = ∑ _a ∈ A, #(midThird p) := by
          refine sum_congr rfl fun a ha => ?_
          rw [← card_filter, filter_erase_zero, card_filter_mul_mem (hane a ha)]
      _ = #A * #(midThird p) := by rw [sum_const, smul_eq_mul]
  have hΘne : ((univ : Finset (ZMod p)).erase 0).Nonempty := by
    rw [← card_pos, card_erase_of_mem (mem_univ 0), card_univ, ZMod.card]
    omega
  -- `#Θ = p - 1` and `p - 1 ≤ 3 * #(midThird p)`, so the mean is at least `#A / 3`.
  have haverage : ∑ _θ ∈ (univ : Finset (ZMod p)).erase 0, #A
      ≤ ∑ θ ∈ (univ : Finset (ZMod p)).erase 0,
          3 * #{a ∈ A | ((Int.cast a : ZMod p) * θ) ∈ midThird p} := by
    rw [sum_const, card_erase_of_mem (mem_univ 0), card_univ, ZMod.card, smul_eq_mul,
      ← mul_sum, hdouble]
    calc (p - 1) * #A ≤ 3 * #(midThird p) * #A :=
          Nat.mul_le_mul_right _ sub_one_le_three_mul_card_midThird
      _ = 3 * (#A * #(midThird p)) := by rw [mul_assoc, Nat.mul_comm (#(midThird p))]
  -- Some `θ` does at least as well as the mean.
  obtain ⟨θ, -, hθle⟩ := Finset.exists_le_of_sum_le hΘne haverage
  refine ⟨{a ∈ A | ((Int.cast a : ZMod p) * θ) ∈ midThird p}, filter_subset _ _, ?_, hθle⟩
  -- An integer sum inside the set would be a sum inside the middle third.
  intro a ha b hb hab
  rw [mem_filter] at ha hb hab
  refine add_notMem_midThird ha.2 hb.2 ?_
  have heq : (Int.cast a : ZMod p) * θ + (Int.cast b : ZMod p) * θ
      = (Int.cast (a + b) : ZMod p) * θ := by
    rw [Int.cast_add, add_mul]
  rw [heq]
  exact hab.2

end PMC
