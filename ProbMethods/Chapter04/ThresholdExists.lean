import ProbMethods.Chapter04.BollobasThomason
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# §4.3 — Theorem 4.3.6, every non-trivial monotone property has a threshold

Zhao, *Probabilistic Methods in Combinatorics*, Definition 4.3.1 and Theorem 4.3.6
(Bollobás–Thomason 1987). `q` is a *threshold* for a sequence of monotone properties when

    P(Ω_{p_n} ∈ F) → 0  whenever  p_n / q_n → 0,      P(Ω_{p_n} ∈ F) → 1  whenever  p_n / q_n → ∞,

and the theorem is that a threshold always exists. The notes single this out as the reason
Lemma 4.3.7 is worth having ("The theorem follows from the next non-asymptotic claim"), so
this file is the asymptotic half of that pair; `PMC.sum_bweight_notMem_le_pow` is the other.

## The route

Take `q n` to be the `p` at which the property has probability exactly `1/2`.

* **It exists.** `p ↦ ∑_{X ∈ F n} bweight p X` is a polynomial in `p`, hence continuous, it is
  `0` at `p = 0` and `1` at `p = 1` — those two endpoint facts are exactly
  `PMC.notMem_empty_of_monotone` and `PMC.mem_univ_of_monotone`, which is what non-triviality
  is for — so the intermediate value theorem supplies `q n ∈ (0,1)` with value `1/2`.
* **Below the threshold.** Fix `m`. Once `p n ≤ q n / m`, antitonicity and Lemma 4.3.7 give

      P(Ω_{p n} ∉ F) ≥ P(Ω_{q n / m} ∉ F) ≥ P(Ω_{q n} ∉ F)^{1/m} = (1/2)^{1/m},

  so `P(Ω_{p n} ∈ F) ≤ 1 - (1/2)^{1/m}`. Letting `m → ∞` after `n → ∞` gives the limit `0`.
* **Above the threshold.** Once `p n ≥ m · q n`, the same lemma read forwards gives

      P(Ω_{p n} ∉ F) ≤ P(Ω_{p n / m} ∉ F)^m ≤ P(Ω_{q n} ∉ F)^m = (1/2)^m,

  so `P(Ω_{p n} ∈ F) ≥ 1 - 2^{-m}`, and again `m → ∞`.

Both directions need `p ↦ P(Ω_p ∉ F)` to be antitone, which is the non-strict form of task
#50, and Lemma 4.3.7, which is task #57. Nothing else.

Remark 4.3.3 in the notes — two thresholds differ by a bounded factor — is not part of this
statement; it is why the notes say "the" threshold.
-/

open Finset

namespace PMC

section ThresholdExists

variable {Ω : ℕ → Type} [∀ n, Fintype (Ω n)] [∀ n, DecidableEq (Ω n)]

/-- **Definition 4.3.1.** `q` is a threshold for the sequence of properties `F`. -/
def IsThreshold (F : ∀ n, Finset (Finset (Ω n))) (q : ℕ → ℝ) : Prop :=
  ∀ p : ℕ → ℝ, (∀ n, p n ∈ Set.Icc (0 : ℝ) 1) →
    (Filter.Tendsto (fun n => p n / q n) Filter.atTop (nhds 0) →
        Filter.Tendsto (fun n => ∑ X ∈ F n, bweight (p n) X) Filter.atTop (nhds 0)) ∧
      (Filter.Tendsto (fun n => p n / q n) Filter.atTop Filter.atTop →
        Filter.Tendsto (fun n => ∑ X ∈ F n, bweight (p n) X) Filter.atTop (nhds 1))

/-- **Theorem 4.3.6 (Bollobás–Thomason 1987).** Every sequence of non-trivial monotone
properties has a threshold. -/
theorem exists_isThreshold (F : ∀ n, Finset (Finset (Ω n)))
    (hmono : ∀ n, IsMonotoneFamily (F n)) (hne : ∀ n, (F n).Nonempty)
    (hnotall : ∀ n, F n ≠ (univ : Finset (Finset (Ω n)))) :
    ∃ q : ℕ → ℝ, (∀ n, q n ∈ Set.Ioo (0 : ℝ) 1) ∧ IsThreshold F q := by
  sorry

end ThresholdExists

end PMC
