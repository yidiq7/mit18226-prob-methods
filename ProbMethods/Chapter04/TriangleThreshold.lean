import ProbMethods.Chapter04.SecondMoment
import ProbMethods.Chapter04.Variance
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# §4.1 — the triangle threshold, as a limit (Proposition 4.1.2)

Zhao, *Probabilistic Methods in Combinatorics*, §4.1. The chapter's quantitative content is
proved elsewhere in explicit form — `PMC.wmean_card_triangles` for the first moment,
`PMC.wvar_card_triangles_le` for the variance, `PMC.sum_bweight_triangleFree_le` for the
second-moment direction. This file states the *asymptotic* half of the threshold, which is
how the notes phrase it, and shows the explicit bounds are strong enough to reach it.

The project's convention is that asymptotic statements are made explicit rather than
deferred. That convention is kept: this file adds a limit statement *on top of* an explicit
bound (`PMC.probHasTriangle_le`) rather than in place of one, and the limit is a two-line
consequence once the bound is there. Nothing about the finite framework has to change to
state `1 - o(1)`: the sample space is `Finset (Sym2 (Fin n))` for each `n`, and the
asymptotics live in `Filter.Tendsto` over `n`.
-/

open Finset Filter

namespace PMC

section TriangleThreshold

/-- The `G(n, p)` probability that the random graph contains a triangle. -/
noncomputable def probHasTriangle (n : ℕ) (p : ℝ) : ℝ :=
  ∑ E ∈ (univ : Finset (Finset (Sym2 (Fin n)))).filter fun E => HasTriangle E, bweight p E

lemma probHasTriangle_nonneg (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ probHasTriangle n p :=
  Finset.sum_nonneg fun E _ => bweight_nonneg hp0 hp1 E

/-- **Markov for triangles**: the chance of containing a triangle is at most the expected
number of them, `C(n,3) p³`. -/
theorem probHasTriangle_le (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    probHasTriangle n p ≤ (n.choose 3 : ℝ) * p ^ 3 := by
  classical
  have hmark := wmarkov (bweight p) (fun E : Finset (Sym2 (Fin n)) => (#(triangles E) : ℝ))
    (fun E => bweight_nonneg hp0 hp1 E) (fun E => by positivity) (a := 1) one_pos
  rw [mul_one, wmean_card_triangles, Fintype.card_fin] at hmark
  refine le_trans (le_of_eq ?_) hmark
  rw [probHasTriangle]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext E
  simp only [mem_filter, mem_univ, true_and, hasTriangle_iff_triangles_nonempty]
  rw [← Finset.card_pos, Nat.one_le_cast, Nat.succ_le_iff]

/-- **Proposition 4.1.2.** If `n p → 0` then `G(n, p)` is triangle-free with probability
`1 - o(1)`.

First moment and Markov: the expected number of triangles is `C(n,3)p³ ≤ (np)³/6`. -/
theorem tendsto_probHasTriangle_zero {p : ℕ → ℝ} (hp0 : ∀ n, 0 ≤ p n) (hp1 : ∀ n, p n ≤ 1)
    (h : Tendsto (fun n : ℕ => (n : ℝ) * p n) atTop (nhds 0)) :
    Tendsto (fun n => probHasTriangle n (p n)) atTop (nhds 0) := by
  have hnn : ∀ n : ℕ, 0 ≤ probHasTriangle n (p n) :=
    fun n => probHasTriangle_nonneg n (hp0 n) (hp1 n)
  have hle : ∀ n : ℕ, probHasTriangle n (p n) ≤ ((n : ℝ) * p n) ^ 3 / 6 := by
    intro n
    refine le_trans (probHasTriangle_le n (hp0 n) (hp1 n)) ?_
    have hchoose : (n.choose 3 : ℝ) ≤ (n : ℝ) ^ 3 / 6 := by
      have h := Nat.choose_le_pow_div (α := ℝ) 3 n
      rw [show ((Nat.factorial 3 : ℕ) : ℝ) = 6 from by simp [Nat.factorial]] at h
      exact h
    have hp3 : (0 : ℝ) ≤ p n ^ 3 := pow_nonneg (hp0 n) 3
    calc (n.choose 3 : ℝ) * p n ^ 3 ≤ ((n : ℝ) ^ 3 / 6) * p n ^ 3 :=
          mul_le_mul_of_nonneg_right hchoose hp3
      _ = ((n : ℝ) * p n) ^ 3 / 6 := by ring
  have hg : Tendsto (fun n : ℕ => ((n : ℝ) * p n) ^ 3 / 6) atTop (nhds 0) := by
    have h3 := h.pow 3
    have := h3.div_const 6
    simpa using this
  exact squeeze_zero hnn hle hg


/-! ### The other half: a triangle appears once `np → ∞` -/

/-- The `G(n, p)` probability that the random graph is triangle-free. -/
noncomputable def probTriangleFree (n : ℕ) (p : ℝ) : ℝ :=
  ∑ E ∈ (univ : Finset (Finset (Sym2 (Fin n)))).filter fun E => ¬ HasTriangle E, bweight p E

lemma probTriangleFree_nonneg (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ probTriangleFree n p :=
  Finset.sum_nonneg fun E _ => bweight_nonneg hp0 hp1 E

/-- **The second-moment bound for triangle-freeness**, multiplicatively:

`P(triangle-free) · (C(n,3)p³)² ≤ C(n,3)(p³ + 3n p⁵)`.

`PMC.sum_bweight_triangleFree_le` at the sharpened variance `PMC.wvar_card_triangles_le'`. -/
theorem probTriangleFree_mul_le (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hmean : 0 < (n.choose 3 : ℝ) * p ^ 3) :
    probTriangleFree n p * ((n.choose 3 : ℝ) * p ^ 3) ^ 2
      ≤ (n.choose 3 : ℝ) * (p ^ 3 + 3 * (n : ℝ) * p ^ 5) := by
  classical
  have hcard : (Fintype.card (Fin n)) = n := Fintype.card_fin n
  have hfree : ∀ E ∈ (univ : Finset (Finset (Sym2 (Fin n)))).filter
      (fun E => ¬ HasTriangle E), triangles E = ∅ := by
    intro E hE
    rw [mem_filter] at hE
    rw [← Finset.not_nonempty_iff_eq_empty, ← hasTriangle_iff_triangles_nonempty]
    exact hE.2
  have h1 := sum_bweight_triangleFree_le (V := Fin n) hp0 hp1 (by rwa [hcard]) hfree
  have h2 := wvar_card_triangles_le' (V := Fin n) hp0 hp1
  rw [hcard] at h1 h2
  exact le_trans h1 h2

/-- `6 C(n,3) = n(n-1)(n-2)`, over `ℝ`, for `n ≥ 2`. The `ℕ` identity is
`Nat.descFactorial`; what this adds is the casts, which need `n ≥ 2` because `ℕ`-subtraction
truncates. -/
lemma choose_three_cast {n : ℕ} (hn : 2 ≤ n) :
    (6 : ℝ) * (n.choose 3 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) := by
  have hdesc : n.descFactorial 3 = 6 * n.choose 3 := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    norm_num [Nat.factorial]
  have hval : n.descFactorial 3 = n * (n - 1) * (n - 2) := by
    simp [Nat.descFactorial]
    ring
  have hcast : ((n * (n - 1) * (n - 2) : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) := by
    have h1 : (1 : ℕ) ≤ n := by omega
    have h2 : (2 : ℕ) ≤ n := by omega
    push_cast [h1, h2]
    ring
  have : ((n.descFactorial 3 : ℕ) : ℝ) = ((6 * n.choose 3 : ℕ) : ℝ) := by rw [hdesc]
  rw [hval, hcast] at this
  push_cast at this
  linarith

/-- `C(n,3) ≥ n³/12` for `n ≥ 6`. -/
private lemma choose_three_ge {n : ℕ} (hn : 6 ≤ n) : (n : ℝ) ^ 3 / 12 ≤ (n.choose 3 : ℝ) := by
  have hnR : (6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  nlinarith [choose_three_cast (n := n) (by omega), hnR]

/-- **Theorem 4.1.11.** If `n p → ∞` then `G(n, p)` contains a triangle with probability
`1 - o(1)`.

The second moment: `P(triangle-free) ≤ 1/(C(n,3)p³) + 3n/(C(n,3)p) ≲ 1/(np)³ + 1/(n²p)`, and
both terms vanish once `np → ∞`, the second because `n²p = n·(np)`.

This is where the sharpened variance earns its keep: the cruder bound
`PMC.wvar_card_triangles_le` gives `1/(n²p³)`, which does not vanish throughout the range
`np → ∞` — at `p = n^{-9/10}` it diverges. -/
theorem tendsto_probTriangleFree_zero {p : ℕ → ℝ} (hp0 : ∀ n, 0 ≤ p n) (hp1 : ∀ n, p n ≤ 1)
    (h : Tendsto (fun n : ℕ => (n : ℝ) * p n) atTop atTop) :
    Tendsto (fun n => probTriangleFree n (p n)) atTop (nhds 0) := by
  set g : ℕ → ℝ := fun n => 12 / ((n : ℝ) * p n) ^ 3 + 36 / ((n : ℝ) * ((n : ℝ) * p n))
    with hgdef
  have hev : ∀ᶠ n : ℕ in atTop, probTriangleFree n (p n) ≤ g n := by
    filter_upwards [eventually_ge_atTop 6, h.eventually_ge_atTop 1] with n hn6 hnp1
    have hnR : (6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn6
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hppos : 0 < p n := by
      rcases lt_or_eq_of_le (hp0 n) with hlt | heq
      · exact hlt
      · rw [← heq, mul_zero] at hnp1
        linarith
    have hchoose : (n : ℝ) ^ 3 / 12 ≤ (n.choose 3 : ℝ) := choose_three_ge hn6
    have hcpos : (0 : ℝ) < (n.choose 3 : ℝ) := by
      have : (0 : ℝ) < (n : ℝ) ^ 3 / 12 := by positivity
      linarith
    have hmean : 0 < (n.choose 3 : ℝ) * p n ^ 3 := by positivity
    have hbound := probTriangleFree_mul_le n (hp0 n) (hp1 n) hmean
    -- divide through by `(C(n,3) p³)²`
    have hsq : (0 : ℝ) < ((n.choose 3 : ℝ) * p n ^ 3) ^ 2 := by positivity
    rw [← le_div_iff₀ hsq] at hbound
    refine le_trans hbound ?_
    have hsplit : (n.choose 3 : ℝ) * (p n ^ 3 + 3 * (n : ℝ) * p n ^ 5)
          / ((n.choose 3 : ℝ) * p n ^ 3) ^ 2
        = 1 / ((n.choose 3 : ℝ) * p n ^ 3) + 3 * (n : ℝ) / ((n.choose 3 : ℝ) * p n) := by
      field_simp
    have hA : (1 : ℝ) / ((n.choose 3 : ℝ) * p n ^ 3) ≤ 12 / ((n : ℝ) * p n) ^ 3 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity),
        show ((n : ℝ) * p n) ^ 3 = (n : ℝ) ^ 3 * p n ^ 3 from by ring]
      nlinarith [hchoose, pow_pos hppos 3]
    have hB : 3 * (n : ℝ) / ((n.choose 3 : ℝ) * p n)
        ≤ 36 / ((n : ℝ) * ((n : ℝ) * p n)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hchoose, hppos, hnpos]
    rw [hsplit]
    simp only [hgdef]
    linarith [hA, hB]
  have hg : Tendsto g atTop (nhds 0) := by
    have hcube : Tendsto (fun n : ℕ => ((n : ℝ) * p n) ^ 3) atTop atTop :=
      (tendsto_pow_atTop (α := ℝ) (n := 3) (by norm_num)).comp h
    have h1 : Tendsto (fun n : ℕ => 12 / ((n : ℝ) * p n) ^ 3) atTop (nhds 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds hcube
    have h2 : Tendsto (fun n : ℕ => 36 / ((n : ℝ) * ((n : ℝ) * p n))) atTop (nhds 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds
        (Filter.Tendsto.atTop_mul_atTop₀ tendsto_natCast_atTop_atTop h)
    have := h1.add h2
    simpa [hgdef] using this
  exact squeeze_zero' (Filter.Eventually.of_forall
    fun n => probTriangleFree_nonneg n (hp0 n) (hp1 n)) hev hg


/-! ### The threshold, in the notes' phrasing

The notes say "with probability `1 - o(1)`", which is the complementary limit. Both forms are
recorded, since `PMC.probHasTriangle_add_probTriangleFree` makes the translation one step. -/

/-- Containing a triangle and being triangle-free are complementary events. -/
theorem probHasTriangle_add_probTriangleFree (n : ℕ) (p : ℝ) :
    probHasTriangle n p + probTriangleFree n p = 1 := by
  classical
  have h := Finset.sum_filter_add_sum_filter_not
    (univ : Finset (Finset (Sym2 (Fin n)))) (fun E => HasTriangle E) (bweight p)
  have htot : ∑ E : Finset (Sym2 (Fin n)), bweight p E = 1 := by
    have h := sum_bweight (α := Sym2 (Fin n)) p
    rwa [Finset.powerset_univ] at h
  rw [probHasTriangle, probTriangleFree, h, htot]

/-- **Proposition 4.1.2, as the notes state it**: if `n p → 0` then `G(n, p)` is triangle-free
with probability `1 - o(1)`. -/
theorem tendsto_probTriangleFree_one {p : ℕ → ℝ} (hp0 : ∀ n, 0 ≤ p n) (hp1 : ∀ n, p n ≤ 1)
    (h : Tendsto (fun n : ℕ => (n : ℝ) * p n) atTop (nhds 0)) :
    Tendsto (fun n => probTriangleFree n (p n)) atTop (nhds 1) := by
  have hsum : ∀ n : ℕ, probTriangleFree n (p n) = 1 - probHasTriangle n (p n) := by
    intro n
    have := probHasTriangle_add_probTriangleFree n (p n)
    linarith
  have := (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ))).sub
    (tendsto_probHasTriangle_zero hp0 hp1 h)
  rw [sub_zero] at this
  exact this.congr fun n => (hsum n).symm

/-- **Theorem 4.1.11, as the notes state it**: if `n p → ∞` then `G(n, p)` contains a triangle
with probability `1 - o(1)`. -/
theorem tendsto_probHasTriangle_one {p : ℕ → ℝ} (hp0 : ∀ n, 0 ≤ p n) (hp1 : ∀ n, p n ≤ 1)
    (h : Tendsto (fun n : ℕ => (n : ℝ) * p n) atTop atTop) :
    Tendsto (fun n => probHasTriangle n (p n)) atTop (nhds 1) := by
  have hsum : ∀ n : ℕ, probHasTriangle n (p n) = 1 - probTriangleFree n (p n) := by
    intro n
    have := probHasTriangle_add_probTriangleFree n (p n)
    linarith
  have := (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ))).sub
    (tendsto_probTriangleFree_zero hp0 hp1 h)
  rw [sub_zero] at this
  exact this.congr fun n => (hsum n).symm


/-! ### Corollary 4.1.8, the asymptotic second moment method

The limit form of `PMC.wsecond_moment`. It is stated over a *family* of spaces `Ω n`, which is
what an asymptotic statement needs — the sample space of `G(n,p)` changes with `n` — and which
costs nothing in Lean. -/

/-- **Corollary 4.1.8** (first half). If the variance is `o` of the squared mean along a
sequence of finite weighted spaces, then the weight of any set where the count vanishes tends
to `0`: the random object contains the structure being counted, whp.

`PMC.wsecond_moment` divided by `(E X)²`, then squeezed. -/
theorem tendsto_wprob_zero_of_var_div_sq_mean {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)]
    [∀ n, DecidableEq (Ω n)] (w : ∀ n, Ω n → ℝ) (X : ∀ n, Ω n → ℝ)
    (hw : ∀ n, ∀ ω, 0 ≤ w n ω) (hmean : ∀ n, 0 < wmean (w n) (X n))
    (S : ∀ n, Finset (Ω n)) (hS : ∀ n, ∀ ω ∈ S n, X n ω = 0)
    (h : Tendsto (fun n => wvar (w n) (X n) / (wmean (w n) (X n)) ^ 2) atTop (nhds 0)) :
    Tendsto (fun n => ∑ ω ∈ S n, w n ω) atTop (nhds 0) := by
  refine squeeze_zero (fun n => Finset.sum_nonneg fun ω _ => hw n ω) (fun n => ?_) h
  have hsq : (0 : ℝ) < (wmean (w n) (X n)) ^ 2 := pow_pos (hmean n) 2
  rw [le_div_iff₀ hsq]
  exact wsecond_moment (w n) (X n) (hw n) (hmean n) (hS n)

end TriangleThreshold

end PMC
