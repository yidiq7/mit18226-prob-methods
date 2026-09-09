import ProbMethods.Weighted

/-!
# §4.2 — the variance of a sum of indicators (Setup 4.2.2)

Zhao, *Probabilistic Methods in Combinatorics*, Setup 4.2.2 and Lemma 4.2.4. The second-moment
method needs the variance of `X = ∑ᵢ 1_{Aᵢ}` for a family of events with a *dependency
structure*: pairs of events that are independent contribute nothing, so

    Var X ≤ E X + ∑ᵢ ∑_{j ∈ N i} P(Aᵢ ∩ A_j),

where `N i` lists the indices `j ≠ i` whose event may depend on `Aᵢ`. The notes write the
second term as `μ Δ*` with `Δ* = maxᵢ ∑_{j ∈ N i} P(A_j | Aᵢ)`; dividing is avoided here by
keeping the double sum, and the `Δ*` form follows by bounding each inner sum.

**Why this is worth having.** Every second-moment threshold in §4.2 and §4.4 — Theorem 4.2.5's
other direction, Theorem 4.2.10's other direction, Theorem 4.4.2(b) — is this bound followed by
`PMC.tendsto_wprob_zero_of_var_div_sq_mean`. §4.1's triangle case was done by hand
(`PMC.wvar_card_triangles_le'`), and that proof is exactly this bound specialised, so having it
once in general is what makes the remaining thresholds reachable.

Note the shape of the independence hypothesis: it constrains only the pairs *outside* the
dependency lists, which is what makes the bound usable — the whole point is that the `N i` are
small and nothing has to be known about the pairs inside them.
-/

open Finset

namespace PMC

section DeltaStar

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The number of events of the family that occur at `ω`. -/
def occCount (A : ι → Finset Ω) (ω : Ω) : ℝ :=
  #((univ : Finset ι).filter fun i => ω ∈ A i)

/-- **Setup 4.2.2's variance bound.** For a family of events whose non-adjacent pairs are
independent,

    Var (∑ᵢ 1_{Aᵢ}) ≤ ∑ᵢ P(Aᵢ) + ∑ᵢ ∑_{j ∈ N i} P(Aᵢ ∩ A_j).

The two terms are the notes' `μ` and `μ Δ*`. The diagonal `i = j` contributes
`P(Aᵢ) - P(Aᵢ)² ≤ P(Aᵢ)`, the independent pairs contribute exactly `0`, and the dependent
pairs are bounded by dropping the `-P(Aᵢ)P(A_j)`. -/
theorem wvar_occCount_le {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω = 1)
    (A : ι → Finset Ω) (N : ι → Finset ι) (hself : ∀ i, i ∉ N i)
    (hindep : ∀ i j, i ≠ j → j ∉ N i →
      wprob w (A i ∩ A j) = wprob w (A i) * wprob w (A j)) :
    wvar w (occCount A) ≤ (∑ i, wprob w (A i)) + ∑ i, ∑ j ∈ N i, wprob w (A i ∩ A j) := by
  sorry

end DeltaStar

end PMC
