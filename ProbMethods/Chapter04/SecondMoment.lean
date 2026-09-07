import ProbMethods.Chapter04.FirstMoment

/-!
# §4.1 — Triangles in a random graph, second moment

Zhao, *Probabilistic Methods in Combinatorics*, §4.1.

The first-moment half (`ProbMethods/Chapter04/FirstMoment.lean`) says a random graph
typically has *no* triangle once `C(n,3) p ^ 3` is small. This is the other half: once the
expected count is large next to its standard deviation, almost all the weight sits on
graphs that *do* contain one.

Stated as a finite inequality, per this project's conventions; the `n → ∞` threshold is not
stated.
-/

open Finset

namespace PMC

/-- The weighted mean of the triangle count in `G(n, p)` is `C(n, 3) * p ^ 3`, in `wmean`
form so that `PMC.wchebyshev` and `PMC.wsecond_moment` apply to it. -/
theorem wmean_card_triangles {V : Type*} [Fintype V] [DecidableEq V] (p : ℝ) :
    wmean (bweight p) (fun E : Finset (Sym2 V) => (#(triangles E) : ℝ))
      = (Fintype.card V).choose 3 * p ^ 3 := by
  rw [wmean_eq_sum_powerset]
  exact sum_bweight_mul_card_triangles p

/-- **The second-moment direction for triangles** (Zhao, §4.1).

Any family of triangle-free graphs carries total `G(n, p)`-weight at most
`Var / (C(n,3) p ^ 3) ^ 2`, stated multiplicatively.

So when the variance is small next to the squared mean, triangle-free graphs are a
vanishing share of the weight — which is the "typically contains a triangle" half of the
threshold. The variance itself is
`∑ t, ∑ t', p ^ #(spannedEdges t ∪ spannedEdges t') - (C(n,3) p ^ 3) ^ 2` by
`PMC.sum_bweight_mul_card_filter_sq`; the overlap analysis that turns that into an explicit
bound is the remaining work in this section. -/
theorem sum_bweight_triangleFree_le {V : Type*} [Fintype V] [DecidableEq V] {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hmean : 0 < ((Fintype.card V).choose 3 : ℝ) * p ^ 3)
    {S : Finset (Finset (Sym2 V))} (hS : ∀ E ∈ S, triangles E = ∅) :
    (∑ E ∈ S, bweight p E) * (((Fintype.card V).choose 3 : ℝ) * p ^ 3) ^ 2
      ≤ wvar (bweight p) (fun E : Finset (Sym2 V) => (#(triangles E) : ℝ)) := by
  have hmean' : 0 < wmean (bweight p) (fun E : Finset (Sym2 V) => (#(triangles E) : ℝ)) := by
    rw [wmean_card_triangles]; exact hmean
  have h := wsecond_moment (bweight p)
    (fun E : Finset (Sym2 V) => (#(triangles E) : ℝ))
    (fun E => bweight_nonneg hp0 hp1 E) hmean'
    (S := S) (fun E hE => by rw [hS E hE, card_empty, Nat.cast_zero])
  rwa [wmean_card_triangles] at h

end PMC
