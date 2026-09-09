import ProbMethods.Weighted
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Moments.SubGaussian

/-!
# The bridge from a finite weight to a measure

This development is deliberately measure-free: a probability distribution on a finite type is
a weight `w : Ω → ℝ` with `w ≥ 0` and `∑ w = 1`, and an expectation is `PMC.wmean`. That
choice pays for itself all through Chapters 1–8 and 10 — but it cuts the project off from
Mathlib's probability library, which is stated for `Measure`.

This file removes that wall. `PMC.wpmf` packages a weight as a `PMF`, and
`PMC.wmean_eq_integral` identifies `PMC.wmean` with the Bochner integral against its measure:

    wmean w f = ∫ ω, f ω ∂(wmeasure w).

Everything else in Mathlib's probability library then applies to a finite weighted space. The
first use is Hoeffding's lemma (`PMC.wmean_exp_le_of_mem_Icc`), whose analytic core —
`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` — is upstream; the same
bridge reaches Azuma–Hoeffding, the sub-Gaussian machinery, and the martingale library.

## What the bridge costs

Two instances, and nothing else. A finite type carries no `MeasurableSpace`, so this file
supplies `⊤` — under which every set is measurable and every function is `Measurable` — and the
`MeasurableSingletonClass` that `PMF.toMeasure`'s lemmas want. Both are as canonical as they
look: on a finite type there is no other reasonable σ-algebra, and picking it explicitly is
what keeps the rest of the development free of measure-theoretic hypotheses.
-/

open Finset MeasureTheory

namespace PMC

section Bridge

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The discrete σ-algebra on a finite type: every set is measurable. Supplied as a `local
instance` so that no other file inherits a measure-theoretic structure it does not want. -/
scoped instance : MeasurableSpace Ω := ⊤

scoped instance : MeasurableSingletonClass Ω := ⟨fun _ => trivial⟩

/-- A finite weight, packaged as a `PMF`. -/
noncomputable def wpmf (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω = 1) : PMF Ω :=
  PMF.ofFintype (fun ω => ENNReal.ofReal (w ω)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun ω _ => hw ω, hsum, ENNReal.ofReal_one])

@[simp] lemma wpmf_apply {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω = 1) (ω : Ω) :
    wpmf w hw hsum ω = ENNReal.ofReal (w ω) := PMF.ofFintype_apply _ _

@[simp] lemma wpmf_apply_toReal {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω = 1) (ω : Ω) :
    (wpmf w hw hsum ω).toReal = w ω := by
  rw [wpmf_apply, ENNReal.toReal_ofReal (hw ω)]

/-- The measure of a finite weight. -/
noncomputable def wmeasure (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω = 1) : Measure Ω :=
  (wpmf w hw hsum).toMeasure

instance isProbabilityMeasure_wmeasure {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (hsum : ∑ ω, w ω = 1) : IsProbabilityMeasure (wmeasure w hw hsum) := by
  rw [wmeasure]
  infer_instance

/-- **The bridge.** `PMC.wmean` is the Bochner integral against `PMC.wmeasure`. -/
theorem wmean_eq_integral {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω = 1)
    (f : Ω → ℝ) : wmean w f = ∫ ω, f ω ∂(wmeasure w hw hsum) := by
  rw [wmeasure, PMF.integral_eq_sum, wmean]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [wpmf_apply_toReal, smul_eq_mul]

end Bridge

end PMC
