import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# §4.7 — the Weierstrass approximation theorem (Theorem 4.7.1)

Zhao, *Probabilistic Methods in Combinatorics*, Theorem 4.7.1: every continuous
`f : [0,1] → ℝ` is uniformly approximated by polynomials.

**This section is upstream.** Mathlib proves it, and proves it by *exactly* the notes'
argument: Bernstein's polynomials `∑ₖ f(k/n) · C(n,k) xᵏ(1-x)^{n-k}`, which is the
expectation of `f` at the empirical mean of `n` independent `Bernoulli(x)` variables, with
the error controlled by Chebyshev's inequality applied to that mean — the same second-moment
argument as the rest of Chapter 4. See `bernsteinApproximation_uniform` and
`Mathlib/Analysis/SpecialFunctions/Bernstein.lean`, whose variance computation
(`bernstein.variance`) is the notes' `Var(X̄) = x(1-x)/n`.

What this file adds is only the bridge: Mathlib states the theorem as "the polynomial
functions are topologically dense in `C([a,b], ℝ)`", and the notes state it as "for every
`ε` there is a polynomial within `ε` uniformly". Unravelling the density into an explicit
`ε` is what an application needs, and doing it once here means no application has to.

Recorded as `upstream`: it must never be published as a task.
-/

open Polynomial

namespace PMC

/-- **The Weierstrass approximation theorem** (Zhao, Theorem 4.7.1), in the notes' form:
for a continuous `f` on `[0,1]` and any `ε > 0` there is a polynomial uniformly within `ε`.

Mathlib's `polynomialFunctions_closure_eq_top` says the polynomial functions are dense in
`C([0,1], ℝ)`; this unravels that density at a single `ε`. -/
theorem exists_polynomial_sup_le (f : C(Set.Icc (0 : ℝ) 1, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ[X], ∀ x : Set.Icc (0 : ℝ) 1, |p.eval (x : ℝ) - f x| ≤ ε := by
  have hmem : f ∈ closure ((polynomialFunctions (Set.Icc (0 : ℝ) 1)) :
      Set C(Set.Icc (0 : ℝ) 1, ℝ)) := by
    rw [show closure ((polynomialFunctions (Set.Icc (0 : ℝ) 1)) :
        Set C(Set.Icc (0 : ℝ) 1, ℝ))
      = ((polynomialFunctions (Set.Icc (0 : ℝ) 1)).topologicalClosure :
        Set C(Set.Icc (0 : ℝ) 1, ℝ)) from rfl, polynomialFunctions_closure_eq_top]
    exact Set.mem_univ _
  obtain ⟨g, hg, hdist⟩ := Metric.mem_closure_iff.mp hmem ε hε
  obtain ⟨p, -, hp⟩ := Subalgebra.mem_map.mp hg
  refine ⟨p, fun x => ?_⟩
  have hx : |g x - f x| ≤ dist g f := by
    rw [← Real.dist_eq]
    exact ContinuousMap.dist_apply_le_dist x
  have hgx : g x = p.eval (x : ℝ) := by rw [← hp]; rfl
  rw [← hgx]
  exact hx.trans (le_of_lt (by rwa [dist_comm] at hdist))

/-- The same statement for a function on `ℝ` continuous on `[0,1]`, which is how the notes
phrase it. -/
theorem exists_polynomial_approx {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1)) {ε : ℝ}
    (hε : 0 < ε) : ∃ p : ℝ[X], ∀ x ∈ Set.Icc (0 : ℝ) 1, |p.eval x - f x| ≤ ε := by
  obtain ⟨p, hp⟩ := exists_polynomial_sup_le ⟨(Set.Icc (0:ℝ) 1).domRestrict f, hf.domRestrict⟩ hε
  exact ⟨p, fun x hx => hp ⟨x, hx⟩⟩

end PMC
