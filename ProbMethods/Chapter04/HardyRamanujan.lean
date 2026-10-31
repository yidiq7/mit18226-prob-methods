import ProbMethods.Weighted
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# §4.5 — Theorem 4.5.1, Hardy–Ramanujan by Turán's second moment

Zhao, *Probabilistic Methods in Combinatorics*, Theorem 4.5.1 (Hardy–Ramanujan 1917, this
proof Turán 1934): for every `ε > 0` there is `C` such that for all large `n`, all but an
`ε`-fraction of `x ∈ [n]` satisfy

    |ν(x) - log log n| ≤ C √(log log n),

where `ν x` is the number of *distinct* prime divisors of `x` (`Nat.primeFactors x |>.card`).

**Mertens' second theorem is an explicit hypothesis**, not an assumption hidden in the proof.
`∑_{p ≤ m} 1/p = log log m + O(1)` is analytic number theory that Mathlib does not have, and
the notes quote it too ("We quote Merten's theorem from analytic number theory"). Naming it in
the statement is the same device used for Harper's inequality in Theorem 4.6.6 and for Theorem
6.5.5 in the Latin-transversal bound: the gap stays visible in the type rather than in prose.
Everything else is the second moment method, which this development already has.

## The route

Sample `x ∈ [n]` uniformly and let `X p` be the indicator of `p ∣ x`. Put `M = n^{1/10}` and
`X = ∑_{p ≤ M} X p`.

* **`ν` and `X` differ by at most `10`.** `ν x - 10 ≤ X x ≤ ν x`, because `x ≤ n` cannot have
  more than `10` prime factors exceeding `n^{1/10}`. So it is enough to concentrate `X`, and
  the additive `10` is absorbed by `C √(log log n)`.
* **First moment.** Exactly `⌊n/p⌋` integers in `[n]` are divisible by `p`, so
  `E[X p] = ⌊n/p⌋/n = 1/p + O(1/n)`, and Mertens gives
  `E X = log log M + O(1) = log log n + O(1)`, since `log log n^{1/10} = log log n - log 10`.
* **Second moment.** For distinct primes `p, q`, `p ∣ x ∧ q ∣ x ↔ pq ∣ x`, so
  `E[X p X q] = ⌊n/pq⌋/n = 1/(pq) + O(1/n)` and the covariance of `X p, X q` is `O(1/n)`. There
  are at most `M² = n^{1/5}` pairs, contributing `O(n^{-4/5})`; the diagonal contributes
  `∑_{p ≤ M} (1/p)(1 - 1/p) ≤ log log n + O(1)`. Hence `Var X = O(log log n)`.
* **Chebyshev.** `PMC.wchebyshev` at deviation `C √(log log n)` gives an exceptional set of
  measure `O(1/C²)`, which is below `ε` once `C` is large — and `C` is allowed to depend on `ε`,
  which is exactly the shape of the statement.

The sample space is `Fin n` (or `Finset.Icc 1 n`) with uniform weights, so `PMC.wmean`,
`PMC.wvar` and `PMC.wchebyshev` apply directly; no measure theory is involved.
-/

open Finset

namespace PMC

section HardyRamanujan

/-- An integer `m` near the tenth root of `n ≥ 2 ^ 10`: `n < m ^ 10`, yet `m ≤ n` and
`m ^ 2 ≤ 4 n`. -/
private lemma exists_near_tenth_root {n : ℕ} (hn : 2 ^ 10 ≤ n) :
    ∃ m : ℕ, 3 ≤ m ∧ m ≤ n ∧ m ^ 2 ≤ 4 * n ∧ n < m ^ 10 := by
  have hex : ∃ m : ℕ, n < m ^ 10 :=
    ⟨n + 1, lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_self_pow (by norm_num) _)⟩
  have hspec : n < Nat.find hex ^ 10 := Nat.find_spec hex
  have h3 : 3 ≤ Nat.find hex := by
    by_contra h
    have hle : Nat.find hex ≤ 2 := by omega
    have := Nat.pow_le_pow_left hle 10
    omega
  obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hmin : k ^ 10 ≤ n := by
    have := Nat.find_min hex (m := k) (by omega)
    omega
  rw [hk] at hspec h3
  have hk2 : 2 ≤ k := by omega
  have hsq : k ^ 2 ≤ k ^ 10 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hlin : k + 1 ≤ k ^ 2 := by nlinarith
  exact ⟨k + 1, h3, by omega, by nlinarith, hspec⟩

/-- Passing from `n` to its approximate tenth root shifts `log log` by at most `log 10`. -/
private lemma log_log_near_tenth_root {n m : ℕ} (hm : 3 ≤ m) (hmn : m ≤ n) (hnm : n < m ^ 10) :
    Real.log (Real.log m) ≤ Real.log (Real.log n) ∧
      Real.log (Real.log n) - Real.log 10 ≤ Real.log (Real.log m) := by
  have hm1 : (1 : ℝ) < m := by exact_mod_cast (by omega : 1 < m)
  have hm0 : (0 : ℝ) < m := by linarith
  have hlogm : 0 < Real.log m := Real.log_pos hm1
  have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hle : Real.log m ≤ Real.log n := Real.log_le_log hm0 hmnR
  have hn0 : (0 : ℝ) < n := by linarith
  have hlt : Real.log n < 10 * Real.log m := by
    have hnmR : (n : ℝ) < (m : ℝ) ^ 10 := by exact_mod_cast hnm
    have h := Real.log_lt_log hn0 hnmR
    rwa [Real.log_pow, Nat.cast_ofNat] at h
  refine ⟨Real.log_le_log hlogm hle, ?_⟩
  have h := Real.log_le_log (lt_of_lt_of_le hlogm hle) hlt.le
  rw [Real.log_mul (by norm_num) hlogm.ne'] at h
  linarith

/-- `log log n ≥ 1` once `n ≥ 2 ^ 10`. -/
private lemma one_le_log_log {n : ℕ} (hn : 2 ^ 10 ≤ n) : 1 ≤ Real.log (Real.log n) := by
  have hnR : (1024 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hexp : Real.exp 1 ≤ 4 := by
    have h := Real.add_one_le_exp (-(1 / 2) : ℝ)
    have h1 : Real.exp (1 / 2) * Real.exp (-(1 / 2)) = 1 := by
      rw [← Real.exp_add]
      simp
    have h2 : Real.exp 1 = Real.exp (1 / 2) * Real.exp (1 / 2) := by
      rw [← Real.exp_add]
      norm_num
    have h3 : 0 < Real.exp (1 / 2) := Real.exp_pos _
    have h4 : Real.exp (1 / 2) ≤ 2 := by nlinarith
    rw [h2]
    nlinarith
  have hexp0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  have hlog : 4 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hn0]
    have h : Real.exp 4 = Real.exp 1 ^ 4 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have h' : Real.exp 1 ^ 4 ≤ 4 ^ 4 := pow_le_pow_left₀ hexp0 hexp 4
    rw [h]
    linarith [(by norm_num : (4 : ℝ) ^ 4 = 256)]
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith

/-- All but at most `9` prime factors of `x ≤ n` lie below `m`, because `c` prime factors `≥ m`
force `m ^ c ≤ x ≤ n < m ^ 10`. -/
private lemma card_primeFactors_near {x n m : ℕ} (hx : x ≠ 0) (hxn : x ≤ n) (hm : 1 < m)
    (hnm : n < m ^ 10) :
    #((Nat.primesBelow m).filter (· ∣ x)) ≤ x.primeFactors.card ∧
      x.primeFactors.card ≤ #((Nat.primesBelow m).filter (· ∣ x)) + 9 := by
  have hset : (Nat.primesBelow m).filter (· ∣ x) = x.primeFactors.filter (· < m) := by
    ext p
    simp only [mem_filter, Nat.mem_primesBelow, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h2, h3, hx⟩, h1⟩
    · rintro ⟨⟨h1, h2, _⟩, h3⟩
      exact ⟨⟨h3, h1⟩, h2⟩
  have hsplit := card_filter_add_card_filter_not (s := x.primeFactors) (· < m)
  have hbig : #(x.primeFactors.filter fun p => ¬ p < m) ≤ 9 := by
    have h1 : m ^ #(x.primeFactors.filter fun p => ¬ p < m)
        ≤ ∏ p ∈ x.primeFactors.filter (fun p => ¬ p < m), p :=
      Finset.pow_card_le_prod _ _ _ fun p hp => not_lt.mp (mem_filter.mp hp).2
    have h2 : ∏ p ∈ x.primeFactors.filter (fun p => ¬ p < m), p ≤ x :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hx)
        ((Finset.prod_dvd_prod_of_subset _ _ _ (filter_subset _ _)).trans
          (Nat.prod_primeFactors_dvd x))
    have h3 : m ^ #(x.primeFactors.filter fun p => ¬ p < m) < m ^ 10 := by omega
    have h4 := (Nat.pow_lt_pow_iff_right hm).mp h3
    omega
  rw [hset]
  omega

/-- Exactly `⌊n / d⌋` integers in `[n]` are divisible by `d`. -/
private lemma sum_indicator_dvd (n d : ℕ) :
    ∑ x ∈ Icc 1 n, (if d ∣ x then (1 : ℝ) else 0) = ((n / d : ℕ) : ℝ) := by
  have h : Icc 1 n = Ioc 0 n := by
    ext x
    simp only [mem_Icc, mem_Ioc]
    omega
  rw [Finset.sum_boole, h, Nat.Ioc_filter_dvd_card_eq_div]

/-- `⌊n / p⌋` lies within `1` of `n / p`. -/
private lemma floor_div_bounds (n : ℕ) {p : ℕ} (hp : 0 < p) :
    (n : ℝ) / p - 1 ≤ ((n / p : ℕ) : ℝ) ∧ ((n / p : ℕ) : ℝ) ≤ (n : ℝ) / p := by
  refine ⟨?_, Nat.cast_div_le⟩
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have h : n < p * (n / p + 1) := Nat.lt_mul_div_succ n hp
  have hR : (n : ℝ) < p * (((n / p : ℕ) : ℝ) + 1) := by exact_mod_cast h
  have h' : (n : ℝ) / p < ((n / p : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hpR]
    linarith
  linarith

/-- **The mean.** `∑ p ∈ S, ⌊n / p⌋ / n` is within `1` of `∑ p ∈ S, 1 / p`. -/
private lemma abs_mean_sub_sum_inv_le {n m : ℕ} (hn : 0 < n) (hmn : m ≤ n) :
    |(∑ p ∈ Nat.primesBelow m, ((n / p : ℕ) : ℝ) / n) - ∑ p ∈ Nat.primesBelow m, (1 : ℝ) / p|
      ≤ 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ p ∈ Nat.primesBelow m,
      |((n / p : ℕ) : ℝ) / n - (1 : ℝ) / p| ≤ 1 / n := by
    intro p hp
    have hp0 : 0 < p := (Nat.prime_of_mem_primesBelow hp).pos
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
    obtain ⟨hlo, hhi⟩ := floor_div_bounds n hp0
    have heq : ((n / p : ℕ) : ℝ) / n - (1 : ℝ) / p = (((n / p : ℕ) : ℝ) - (n : ℝ) / p) / n := by
      field_simp
    rw [heq, abs_div, abs_of_pos hnR]
    refine div_le_div_of_nonneg_right ?_ hnR.le
    rw [abs_le]
    constructor <;> linarith
  have hcard : (#(Nat.primesBelow m) : ℝ) ≤ n := by
    have h : #(Nat.primesBelow m) ≤ m := by
      have := card_filter_le (range m) Nat.Prime
      rwa [card_range] at this
    exact_mod_cast h.trans hmn
  calc ∑ p ∈ Nat.primesBelow m, |((n / p : ℕ) : ℝ) / n - (1 : ℝ) / p|
      ≤ ∑ _p ∈ Nat.primesBelow m, (1 : ℝ) / n := Finset.sum_le_sum hterm
    _ = (#(Nat.primesBelow m) : ℝ) * (1 / n) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (n : ℝ) * (1 / n) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 1 := by field_simp

/-- **The covariance of two divisibility indicators**, in counting form: `n / p` on the
diagonal plus an error of at most `1`, and that error alone off the diagonal. -/
private lemma sum_indicator_cov_le {n p q : ℕ} (hn : 0 < n) (hp : p.Prime) (hq : q.Prime)
    (hpn : p ≤ n) (hqn : q ≤ n) :
    ∑ x ∈ Icc 1 n, ((if p ∣ x then (1 : ℝ) else 0) - ((n / p : ℕ) : ℝ) / n)
        * ((if q ∣ x then (1 : ℝ) else 0) - ((n / q : ℕ) : ℝ) / n)
      ≤ (if p = q then (n : ℝ) / p else 0) + 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  set Np : ℝ := ((n / p : ℕ) : ℝ) with hNp
  set Nq : ℝ := ((n / q : ℕ) : ℝ) with hNq
  have hNp0 : 0 ≤ Np := Nat.cast_nonneg _
  have hNq0 : 0 ≤ Nq := Nat.cast_nonneg _
  have hexpand : ∀ x, ((if p ∣ x then (1 : ℝ) else 0) - Np / n)
      * ((if q ∣ x then (1 : ℝ) else 0) - Nq / n)
        = (if p ∣ x then (1 : ℝ) else 0) * (if q ∣ x then (1 : ℝ) else 0)
          - Nq / n * (if p ∣ x then (1 : ℝ) else 0)
          - Np / n * (if q ∣ x then (1 : ℝ) else 0) + Np / n * (Nq / n) := by
    intro x
    ring
  have hsum : ∑ x ∈ Icc 1 n, ((if p ∣ x then (1 : ℝ) else 0) - Np / n)
      * ((if q ∣ x then (1 : ℝ) else 0) - Nq / n)
        = ∑ x ∈ Icc 1 n, (if p ∣ x then (1 : ℝ) else 0) * (if q ∣ x then (1 : ℝ) else 0)
          - Np * Nq / n := by
    rw [Finset.sum_congr rfl fun x _ => hexpand x, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      sum_indicator_dvd, sum_indicator_dvd, Finset.sum_const, nsmul_eq_mul, Nat.card_Icc,
      Nat.add_sub_cancel, ← hNp, ← hNq]
    field_simp
    ring
  rw [hsum]
  have hmulnn : 0 ≤ Np * Nq / n := by positivity
  by_cases hpq : p = q
  · subst hpq
    have hidem : ∀ x, (if p ∣ x then (1 : ℝ) else 0) * (if p ∣ x then (1 : ℝ) else 0)
        = (if p ∣ x then (1 : ℝ) else 0) := by
      intro x
      by_cases h : p ∣ x <;> simp [h]
    rw [Finset.sum_congr rfl fun x _ => hidem x, sum_indicator_dvd, if_pos rfl]
    have := (floor_div_bounds n hp.pos).2
    linarith
  · rw [if_neg hpq]
    have hprod : ∀ x, (if p ∣ x then (1 : ℝ) else 0) * (if q ∣ x then (1 : ℝ) else 0)
        = (if p * q ∣ x then (1 : ℝ) else 0) := by
      intro x
      have hcop : p.Coprime q := (Nat.coprime_primes hp hq).mpr hpq
      by_cases h1 : p ∣ x
      · by_cases h2 : q ∣ x
        · simp [h1, h2, hcop.mul_dvd_of_dvd_of_dvd h1 h2]
        · have h3 : ¬ p * q ∣ x := fun h => h2 ((Dvd.intro_left p rfl).trans h)
          simp [h2, h3]
      · have h3 : ¬ p * q ∣ x := fun h => h1 ((Dvd.intro q rfl).trans h)
        simp [h1, h3]
    rw [Finset.sum_congr rfl fun x _ => hprod x, sum_indicator_dvd]
    have hpq0 : 0 < p * q := Nat.mul_pos hp.pos hq.pos
    have hc := (floor_div_bounds n hpq0).2
    obtain ⟨hplo, -⟩ := floor_div_bounds n hp.pos
    obtain ⟨hqlo, -⟩ := floor_div_bounds n hq.pos
    rw [← hNp] at hplo
    rw [← hNq] at hqlo
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
    have hpnR : (p : ℝ) ≤ n := by exact_mod_cast hpn
    have hqnR : (q : ℝ) ≤ n := by exact_mod_cast hqn
    have hu : (1 : ℝ) ≤ (n : ℝ) / p := by rwa [one_le_div hp0]
    have hv : (1 : ℝ) ≤ (n : ℝ) / q := by rwa [one_le_div hq0]
    have hu2 : (n : ℝ) / p ≤ n / 2 := div_le_div_of_nonneg_left hnR.le (by norm_num) hp2
    have hv2 : (n : ℝ) / q ≤ n / 2 := div_le_div_of_nonneg_left hnR.le (by norm_num) hq2
    have hNN : ((n : ℝ) / p - 1) * ((n : ℝ) / q - 1) ≤ Np * Nq :=
      mul_le_mul hplo hqlo (by linarith) hNp0
    have hcR : (((p * q : ℕ) : ℝ)) = (p : ℝ) * q := by push_cast; ring
    rw [hcR] at hc
    have hkey : (n : ℝ) / ((p : ℝ) * q) = ((n : ℝ) / p) * ((n : ℝ) / q) / n := by
      field_simp
    have hdiv : ((n : ℝ) / p - 1) * ((n : ℝ) / q - 1) / n ≤ Np * Nq / n :=
      div_le_div_of_nonneg_right hNN hnR.le
    have hexp : ((n : ℝ) / p) * ((n : ℝ) / q) / n
        ≤ ((n : ℝ) / p - 1) * ((n : ℝ) / q - 1) / n + 1 := by
      rw [div_add_one hnR.ne']
      refine div_le_div_of_nonneg_right ?_ hnR.le
      nlinarith
    linarith

/-- **The second moment.** Expanding the square into covariances of divisibility indicators,
the total squared deviation of `X` from its mean is at most `n ∑ 1 / p + m ^ 2`. -/
private lemma sum_sq_deviation_le {n m : ℕ} (hn : 0 < n) (hmn : m ≤ n) :
    ∑ x ∈ Icc 1 n, ((#((Nat.primesBelow m).filter (· ∣ x)) : ℝ)
        - ∑ p ∈ Nat.primesBelow m, ((n / p : ℕ) : ℝ) / n) ^ 2
      ≤ n * ∑ p ∈ Nat.primesBelow m, (1 : ℝ) / p + (m : ℝ) ^ 2 := by
  have hdev : ∀ x, (#((Nat.primesBelow m).filter (· ∣ x)) : ℝ)
        - ∑ p ∈ Nat.primesBelow m, ((n / p : ℕ) : ℝ) / n
      = ∑ p ∈ Nat.primesBelow m, ((if p ∣ x then (1 : ℝ) else 0) - ((n / p : ℕ) : ℝ) / n) := by
    intro x
    rw [Finset.sum_sub_distrib, Finset.sum_boole]
  have hsq : ∑ x ∈ Icc 1 n, ((#((Nat.primesBelow m).filter (· ∣ x)) : ℝ)
        - ∑ p ∈ Nat.primesBelow m, ((n / p : ℕ) : ℝ) / n) ^ 2
      = ∑ p ∈ Nat.primesBelow m, ∑ q ∈ Nat.primesBelow m, ∑ x ∈ Icc 1 n,
          ((if p ∣ x then (1 : ℝ) else 0) - ((n / p : ℕ) : ℝ) / n)
            * ((if q ∣ x then (1 : ℝ) else 0) - ((n / q : ℕ) : ℝ) / n) := by
    calc ∑ x ∈ Icc 1 n, ((#((Nat.primesBelow m).filter (· ∣ x)) : ℝ)
          - ∑ p ∈ Nat.primesBelow m, ((n / p : ℕ) : ℝ) / n) ^ 2
        = ∑ x ∈ Icc 1 n, ∑ p ∈ Nat.primesBelow m, ∑ q ∈ Nat.primesBelow m,
            ((if p ∣ x then (1 : ℝ) else 0) - ((n / p : ℕ) : ℝ) / n)
              * ((if q ∣ x then (1 : ℝ) else 0) - ((n / q : ℕ) : ℝ) / n) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [hdev x, sq, Finset.sum_mul_sum]
      _ = ∑ p ∈ Nat.primesBelow m, ∑ x ∈ Icc 1 n, ∑ q ∈ Nat.primesBelow m,
            ((if p ∣ x then (1 : ℝ) else 0) - ((n / p : ℕ) : ℝ) / n)
              * ((if q ∣ x then (1 : ℝ) else 0) - ((n / q : ℕ) : ℝ) / n) := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun p _ => Finset.sum_comm
  rw [hsq]
  have hcard : (#(Nat.primesBelow m) : ℝ) ≤ m := by
    have h : #(Nat.primesBelow m) ≤ m := by
      have := card_filter_le (range m) Nat.Prime
      rwa [card_range] at this
    exact_mod_cast h
  have hrow : ∀ p ∈ Nat.primesBelow m,
      ∑ q ∈ Nat.primesBelow m, ∑ x ∈ Icc 1 n,
          ((if p ∣ x then (1 : ℝ) else 0) - ((n / p : ℕ) : ℝ) / n)
            * ((if q ∣ x then (1 : ℝ) else 0) - ((n / q : ℕ) : ℝ) / n)
        ≤ n * ((1 : ℝ) / p) + #(Nat.primesBelow m) := by
    intro p hp
    have hpm := Nat.lt_of_mem_primesBelow hp
    calc ∑ q ∈ Nat.primesBelow m, ∑ x ∈ Icc 1 n,
          ((if p ∣ x then (1 : ℝ) else 0) - ((n / p : ℕ) : ℝ) / n)
            * ((if q ∣ x then (1 : ℝ) else 0) - ((n / q : ℕ) : ℝ) / n)
        ≤ ∑ q ∈ Nat.primesBelow m, ((if p = q then (n : ℝ) / p else 0) + 1) :=
          Finset.sum_le_sum fun q hq =>
            sum_indicator_cov_le hn (Nat.prime_of_mem_primesBelow hp)
              (Nat.prime_of_mem_primesBelow hq) (by omega)
              (by have := Nat.lt_of_mem_primesBelow hq; omega)
      _ = n * ((1 : ℝ) / p) + #(Nat.primesBelow m) := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos hp, Finset.sum_const,
            nsmul_eq_mul, mul_one, mul_one_div]
  calc ∑ p ∈ Nat.primesBelow m, ∑ q ∈ Nat.primesBelow m, ∑ x ∈ Icc 1 n,
        ((if p ∣ x then (1 : ℝ) else 0) - ((n / p : ℕ) : ℝ) / n)
          * ((if q ∣ x then (1 : ℝ) else 0) - ((n / q : ℕ) : ℝ) / n)
      ≤ ∑ p ∈ Nat.primesBelow m, (n * ((1 : ℝ) / p) + #(Nat.primesBelow m)) :=
        Finset.sum_le_sum hrow
    _ = n * ∑ p ∈ Nat.primesBelow m, (1 : ℝ) / p
          + (#(Nat.primesBelow m) : ℝ) * #(Nat.primesBelow m) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    _ ≤ n * ∑ p ∈ Nat.primesBelow m, (1 : ℝ) / p + (m : ℝ) ^ 2 := by
        have h0 : (0 : ℝ) ≤ #(Nat.primesBelow m) := Nat.cast_nonneg _
        have : (#(Nat.primesBelow m) : ℝ) * #(Nat.primesBelow m) ≤ (m : ℝ) ^ 2 := by
          rw [sq]
          exact mul_le_mul hcard hcard h0 (h0.trans hcard)
        linarith

/-- **Chebyshev's inequality** for a plain sum over a finite set. -/
private lemma card_filter_lt_abs_mul_sq_le (s : Finset ℕ) (f : ℕ → ℝ) {a : ℝ} (ha : 0 < a) :
    (#(s.filter fun x => a < |f x|) : ℝ) * a ^ 2 ≤ ∑ x ∈ s, f x ^ 2 := by
  calc (#(s.filter fun x => a < |f x|) : ℝ) * a ^ 2
      = ∑ _x ∈ s.filter (fun x => a < |f x|), a ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ x ∈ s.filter (fun x => a < |f x|), f x ^ 2 := by
        refine Finset.sum_le_sum fun x hx => ?_
        rw [← sq_abs (f x)]
        exact pow_le_pow_left₀ ha.le (mem_filter.mp hx).2.le 2
    _ ≤ ∑ x ∈ s, f x ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => sq_nonneg _

/-- The triangle inequality chain: `ν x` is within `10 + B + log 10` of `log log n`, up to the
deviation of `X x` from its mean. -/
private lemma abs_card_primeFactors_sub_log_log_le {n m x : ℕ} {B : ℝ} (hm3 : 3 ≤ m)
    (hmn : m ≤ n) (hnm : n < m ^ 10) (hx : x ∈ Icc 1 n)
    (hB : |(∑ p ∈ Nat.primesBelow m, (1 : ℝ) / p) - Real.log (Real.log m)| ≤ B) :
    |(x.primeFactors.card : ℝ) - Real.log (Real.log n)|
      ≤ (10 + B + Real.log 10)
        + |(#((Nat.primesBelow m).filter (· ∣ x)) : ℝ)
            - ∑ p ∈ Nat.primesBelow m, ((n / p : ℕ) : ℝ) / n| := by
  obtain ⟨hx1, hxn⟩ := mem_Icc.mp hx
  have hn : 0 < n := by omega
  obtain ⟨hlo, hhi⟩ := card_primeFactors_near (x := x) (by omega) hxn (by omega) hnm
  have hloR : (#((Nat.primesBelow m).filter (· ∣ x)) : ℝ) ≤ x.primeFactors.card := by
    exact_mod_cast hlo
  have hhiR : (x.primeFactors.card : ℝ) ≤ #((Nat.primesBelow m).filter (· ∣ x)) + 9 := by
    exact_mod_cast hhi
  obtain ⟨hll1, hll2⟩ := log_log_near_tenth_root hm3 hmn hnm
  obtain ⟨hmean1, hmean2⟩ := abs_le.mp (abs_mean_sub_sum_inv_le hn hmn)
  obtain ⟨hB1, hB2⟩ := abs_le.mp hB
  have h1 := le_abs_self ((#((Nat.primesBelow m).filter (· ∣ x)) : ℝ)
    - ∑ p ∈ Nat.primesBelow m, ((n / p : ℕ) : ℝ) / n)
  have h2 := neg_abs_le ((#((Nat.primesBelow m).filter (· ∣ x)) : ℝ)
    - ∑ p ∈ Nat.primesBelow m, ((n / p : ℕ) : ℝ) / n)
  have hlog10 : 0 ≤ Real.log 10 := Real.log_nonneg (by norm_num)
  rw [abs_le]
  constructor <;> linarith

/-- **Theorem 4.5.1** (Hardy–Ramanujan; Turán's proof), with Mertens' second theorem as an
explicit hypothesis: for every `ε > 0` there is a `C` such that for all large `n`, at most an
`ε`-fraction of `x ∈ [n]` have `|ν(x) - log log n| > C √(log log n)`. -/
theorem hardy_ramanujan {ε : ℝ} (hε : 0 < ε)
    (mertens : ∃ B : ℝ, ∀ m : ℕ, 3 ≤ m →
      |(∑ p ∈ Nat.primesBelow m, (1 : ℝ) / p) - Real.log (Real.log m)| ≤ B) :
    ∃ C > 0, ∃ N : ℕ, ∀ n ≥ N,
      (#((Finset.Icc 1 n).filter fun x =>
          C * Real.sqrt (Real.log (Real.log n))
            < |(x.primeFactors.card : ℝ) - Real.log (Real.log n)|) : ℝ)
        ≤ ε * n := by
  obtain ⟨B, hB⟩ := mertens
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 3 le_rfl)
  have hK0 : 0 ≤ 10 + B + Real.log 10 := by positivity
  have hA0 : 0 ≤ Real.sqrt ((B + 5) / ε) := Real.sqrt_nonneg _
  refine ⟨(10 + B + Real.log 10) + (1 + Real.sqrt ((B + 5) / ε)), by positivity, 2 ^ 10,
    fun n hn => ?_⟩
  obtain ⟨m, hm3, hmn, hm2, hnm⟩ := exists_near_tenth_root hn
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hT : 1 ≤ Real.log (Real.log n) := one_le_log_log hn
  have hT0 : 0 < Real.log (Real.log n) := by linarith
  have hsqrtT : 1 ≤ Real.sqrt (Real.log (Real.log n)) := Real.one_le_sqrt.mpr hT
  have hsqT : Real.sqrt (Real.log (Real.log n)) ^ 2 = Real.log (Real.log n) :=
    Real.sq_sqrt hT0.le
  have hA2 : Real.sqrt ((B + 5) / ε) ^ 2 = (B + 5) / ε := Real.sq_sqrt (by positivity)
  have ha : 0 < (1 + Real.sqrt ((B + 5) / ε)) * Real.sqrt (Real.log (Real.log n)) := by
    positivity
  have hsub : (Finset.Icc 1 n).filter (fun x =>
        ((10 + B + Real.log 10) + (1 + Real.sqrt ((B + 5) / ε)))
            * Real.sqrt (Real.log (Real.log n))
          < |(x.primeFactors.card : ℝ) - Real.log (Real.log n)|)
      ⊆ (Finset.Icc 1 n).filter (fun x =>
        (1 + Real.sqrt ((B + 5) / ε)) * Real.sqrt (Real.log (Real.log n))
          < |(#((Nat.primesBelow m).filter (· ∣ x)) : ℝ)
              - ∑ p ∈ Nat.primesBelow m, ((n / p : ℕ) : ℝ) / n|) := by
    intro x hx
    obtain ⟨hxI, hxbad⟩ := mem_filter.mp hx
    refine mem_filter.mpr ⟨hxI, ?_⟩
    have hdev := abs_card_primeFactors_sub_log_log_le hm3 hmn hnm hxI (hB m hm3)
    have hK : 10 + B + Real.log 10
        ≤ (10 + B + Real.log 10) * Real.sqrt (Real.log (Real.log n)) :=
      le_mul_of_one_le_right hK0 hsqrtT
    rw [add_mul] at hxbad
    linarith
  have hcheb := card_filter_lt_abs_mul_sq_le (Finset.Icc 1 n)
    (fun x => (#((Nat.primesBelow m).filter (· ∣ x)) : ℝ)
      - ∑ p ∈ Nat.primesBelow m, ((n / p : ℕ) : ℝ) / n) ha
  have hsecond := sum_sq_deviation_le hn0 hmn
  have hm2R : (m : ℝ) ^ 2 ≤ 4 * n := by exact_mod_cast hm2
  have hsigma : ∑ p ∈ Nat.primesBelow m, (1 : ℝ) / p ≤ Real.log (Real.log n) + B := by
    have h1 := (abs_le.mp (hB m hm3)).2
    have h2 := (log_log_near_tenth_root hm3 hmn hnm).1
    linarith
  have hupper : ∑ x ∈ Icc 1 n, ((#((Nat.primesBelow m).filter (· ∣ x)) : ℝ)
        - ∑ p ∈ Nat.primesBelow m, ((n / p : ℕ) : ℝ) / n) ^ 2
      ≤ n * ((B + 5) * Real.log (Real.log n)) := by
    have h3 : Real.log (Real.log n) + B + 4 ≤ (B + 5) * Real.log (Real.log n) := by nlinarith
    have h4 : (n : ℝ) * ∑ p ∈ Nat.primesBelow m, (1 : ℝ) / p ≤ n * (Real.log (Real.log n) + B) :=
      mul_le_mul_of_nonneg_left hsigma hnR.le
    have h5 : (n : ℝ) * (Real.log (Real.log n) + B + 4)
        ≤ n * ((B + 5) * Real.log (Real.log n)) := mul_le_mul_of_nonneg_left h3 hnR.le
    linarith
  set Y : ℝ := (#((Finset.Icc 1 n).filter (fun x =>
        ((10 + B + Real.log 10) + (1 + Real.sqrt ((B + 5) / ε)))
            * Real.sqrt (Real.log (Real.log n))
          < |(x.primeFactors.card : ℝ) - Real.log (Real.log n)|)) : ℝ) with hY
  have hYle : Y ≤ (#((Finset.Icc 1 n).filter (fun x =>
        (1 + Real.sqrt ((B + 5) / ε)) * Real.sqrt (Real.log (Real.log n))
          < |(#((Nat.primesBelow m).filter (· ∣ x)) : ℝ)
              - ∑ p ∈ Nat.primesBelow m, ((n / p : ℕ) : ℝ) / n|)) : ℝ) :=
    Nat.cast_le.mpr (card_le_card hsub)
  have hasq : (B + 5) / ε * Real.log (Real.log n)
      ≤ ((1 + Real.sqrt ((B + 5) / ε)) * Real.sqrt (Real.log (Real.log n))) ^ 2 := by
    have hone : (B + 5) / ε ≤ (1 + Real.sqrt ((B + 5) / ε)) ^ 2 := by
      have h : (1 + Real.sqrt ((B + 5) / ε)) ^ 2
          = 1 + 2 * Real.sqrt ((B + 5) / ε) + Real.sqrt ((B + 5) / ε) ^ 2 := by ring
      rw [h, hA2]
      linarith
    rw [mul_pow, hsqT]
    exact mul_le_mul_of_nonneg_right hone hT0.le
  have hfinal : Y * ((B + 5) / ε * Real.log (Real.log n))
      ≤ n * ((B + 5) * Real.log (Real.log n)) := by
    calc Y * ((B + 5) / ε * Real.log (Real.log n))
        ≤ (#((Finset.Icc 1 n).filter (fun x =>
              (1 + Real.sqrt ((B + 5) / ε)) * Real.sqrt (Real.log (Real.log n))
                < |(#((Nat.primesBelow m).filter (· ∣ x)) : ℝ)
                    - ∑ p ∈ Nat.primesBelow m, ((n / p : ℕ) : ℝ) / n|)) : ℝ)
            * ((1 + Real.sqrt ((B + 5) / ε)) * Real.sqrt (Real.log (Real.log n))) ^ 2 :=
          mul_le_mul hYle hasq (by positivity) (Nat.cast_nonneg _)
      _ ≤ _ := hcheb.trans hupper
  have hD : 0 < (B + 5) * Real.log (Real.log n) := by positivity
  have hrearr : Y * ((B + 5) * Real.log (Real.log n))
      ≤ (ε * n) * ((B + 5) * Real.log (Real.log n)) := by
    have h : Y * ((B + 5) / ε * Real.log (Real.log n)) * ε
        = Y * ((B + 5) * Real.log (Real.log n)) := by
      field_simp
    calc Y * ((B + 5) * Real.log (Real.log n))
        = Y * ((B + 5) / ε * Real.log (Real.log n)) * ε := h.symm
      _ ≤ n * ((B + 5) * Real.log (Real.log n)) * ε :=
          mul_le_mul_of_nonneg_right hfinal hε.le
      _ = (ε * n) * ((B + 5) * Real.log (Real.log n)) := by ring
  exact le_of_mul_le_mul_right hrearr hD

end HardyRamanujan

end PMC
