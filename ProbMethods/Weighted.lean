import ProbMethods.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# Weighted counting over a finite space

Shared infrastructure for the results whose distribution is not uniform. Chapters 1 and 2
are all uniform counting; from §3.1 onwards the parameter is a real number, and the device
that carries those arguments is a finite *weighted* sum rather than measure theory.

The point is that over a finite space an expectation is a finite sum, so nothing here needs
`MeasureTheory` or `PMF`. Weights are an arbitrary nonnegative `w : Ω → ℝ`; the results
that need `∑ w = 1` take it as a hypothesis rather than baking it in, since the Bernoulli
weights of §3.1 and the `G(n, p)` weights of Chapter 4 both arrive as products and are
easier to normalise at the point of use.

## Main definitions

* `PMC.wmean` — the weighted mean of a real random variable.
* `PMC.wvar` — its weighted variance, about its own weighted mean.

* `PMC.bweight` — the Bernoulli weight of a subset, `p ^ #X * (1 - p) ^ (card - #X)`.
  Taking `α := Sym2 V` makes this the `G(n, p)` distribution on graphs, which is how
  Chapters 4, 8 and 9 reach the random graph without any measure theory.

## Main results

* `PMC.wchebyshev` — Chebyshev's inequality. Mathlib's Chebyshev is stated for
  `MeasureTheory`/`ProbabilityTheory` and does not apply to a bare finite weighted sum, so
  this is proved here. Chapters 4 (§4.5, §4.6), 5 and 9 all want it.
* `PMC.wmarkov` — Markov's inequality for a nonnegative variable.
* `PMC.wsecond_moment` — **the second moment method**: wherever a count vanishes, the total
  weight is at most `wvar / (wmean) ^ 2`. This is the "whp the count is positive" direction
  of every threshold result, in finite form.
* `PMC.sum_bweight` — the weights total `1`.
* `PMC.sum_bweight_superset` — the subsets *containing* a fixed `B` carry weight `p ^ #B`.
  On `Sym2 V` this is exactly "every edge of a fixed subgraph is present with probability
  `p ^ (its edge count)`", the fact every first-moment random-graph argument opens with.
* `PMC.sum_bweight_disjoint` — the subsets *avoiding* `B` carry weight `(1 - p) ^ #B`.

* `PMC.sum_bweight_mul_card_filter` — **the first moment method**, once and for all: if
  every pattern in a family has `m` elements, the weighted expected number of patterns
  contained in a random subset is `#patterns * p ^ m`. Chapter 4's §4.1, §4.2 and §4.4 are
  all this lemma with different pattern families.
* `PMC.sum_bweight_mul_card_filter_sq` — **the second moment**, in the same generality: the
  weighted mean of the *square* of the pattern count is `∑ i, ∑ j, p ^ #(g i ∪ g j)`. Two
  patterns are both present exactly when their union is, so no new weight computation is
  needed. Feeding this and the first moment into `wchebyshev` is the second-moment method.

`ProbMethods/Chapter03/Dominating.lean` proves private special cases of the disjoint and
superset lemmas; those should be golfed away in favour of these.
-/

open Finset

namespace PMC

section Weighted

variable {Ω : Type*} [Fintype Ω]

/-- The weighted mean of `X` against weights `w`. -/
def wmean (w : Ω → ℝ) (X : Ω → ℝ) : ℝ := ∑ ω, w ω * X ω

/-- The weighted variance of `X`, taken about its own weighted mean. -/
def wvar (w : Ω → ℝ) (X : Ω → ℝ) : ℝ := ∑ ω, w ω * (X ω - wmean w X) ^ 2

lemma wvar_nonneg {w : Ω → ℝ} (X : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) : 0 ≤ wvar w X :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (hw ω) (sq_nonneg _)

/-- **Chebyshev's inequality**, over a finite weighted space.

The total weight of the points where `X` deviates from its weighted mean by at least `a` is
at most `wvar w X / a ^ 2`. Stated multiplicatively so no division or positivity side
condition on the variance is needed. -/
theorem wchebyshev (w : Ω → ℝ) (X : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) {a : ℝ} (ha : 0 < a) :
    (∑ ω ∈ univ.filter fun ω => a ≤ |X ω - wmean w X|, w ω) * a ^ 2 ≤ wvar w X := by
  have hstep : ∀ ω ∈ univ.filter fun ω => a ≤ |X ω - wmean w X|,
      w ω * a ^ 2 ≤ w ω * (X ω - wmean w X) ^ 2 := by
    intro ω hω
    rw [mem_filter] at hω
    refine mul_le_mul_of_nonneg_left ?_ (hw ω)
    calc a ^ 2 ≤ |X ω - wmean w X| ^ 2 := pow_le_pow_left₀ ha.le hω.2 2
      _ = (X ω - wmean w X) ^ 2 := sq_abs _
  calc (∑ ω ∈ univ.filter fun ω => a ≤ |X ω - wmean w X|, w ω) * a ^ 2
      = ∑ ω ∈ univ.filter fun ω => a ≤ |X ω - wmean w X|, w ω * a ^ 2 := Finset.sum_mul _ _ _
    _ ≤ ∑ ω ∈ univ.filter fun ω => a ≤ |X ω - wmean w X|,
          w ω * (X ω - wmean w X) ^ 2 := Finset.sum_le_sum hstep
    _ ≤ ∑ ω, w ω * (X ω - wmean w X) ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun ω _ _ => ?_
        exact mul_nonneg (hw ω) (sq_nonneg _)
    _ = wvar w X := rfl

/-- The complementary form: the weight of the points *within* `a` of the mean is at least
`total - wvar / a ^ 2`. This is the direction §4.6 uses. -/
theorem wchebyshev' (w : Ω → ℝ) (X : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) {a : ℝ} (ha : 0 < a) :
    (∑ ω, w ω) * a ^ 2 - wvar w X
      ≤ (∑ ω ∈ univ.filter fun ω => |X ω - wmean w X| < a, w ω) * a ^ 2 := by
  have h := wchebyshev w X hw ha
  have hfar : (univ.filter fun ω => ¬ |X ω - wmean w X| < a)
      = univ.filter fun ω => a ≤ |X ω - wmean w X| := by
    ext ω; simp [not_lt]
  have hsplit := Finset.sum_filter_add_sum_filter_not (univ : Finset Ω)
    (fun ω => |X ω - wmean w X| < a) w
  rw [hfar] at hsplit
  have hT : (∑ ω, w ω) * a ^ 2
      = (∑ ω ∈ univ.filter fun ω => |X ω - wmean w X| < a, w ω) * a ^ 2
        + (∑ ω ∈ univ.filter fun ω => a ≤ |X ω - wmean w X|, w ω) * a ^ 2 := by
    rw [← add_mul, hsplit]
  linarith

/-- **Markov's inequality** over a finite weighted space.

The total weight of the points where a nonnegative `X` reaches `a` is at most
`wmean w X / a`. Stated multiplicatively. Mathlib's Markov is `MeasureTheory`-only. -/
theorem wmarkov (w : Ω → ℝ) (X : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hX : ∀ ω, 0 ≤ X ω)
    {a : ℝ} (ha : 0 < a) :
    (∑ ω ∈ univ.filter fun ω => a ≤ X ω, w ω) * a ≤ wmean w X := by
  calc (∑ ω ∈ univ.filter fun ω => a ≤ X ω, w ω) * a
      = ∑ ω ∈ univ.filter fun ω => a ≤ X ω, w ω * a := Finset.sum_mul _ _ _
    _ ≤ ∑ ω ∈ univ.filter fun ω => a ≤ X ω, w ω * X ω := by
        refine Finset.sum_le_sum fun ω hω => ?_
        rw [mem_filter] at hω
        exact mul_le_mul_of_nonneg_left hω.2 (hw ω)
    _ ≤ ∑ ω, w ω * X ω := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun ω _ _ => ?_
        exact mul_nonneg (hw ω) (hX ω)
    _ = wmean w X := rfl

/-- **The second moment method.**

If a count `N` has positive weighted mean, then any set of points where `N` vanishes has
total weight at most `wvar w N / (wmean w N) ^ 2`. Stated multiplicatively, so there is no
division and no need to know the variance is nonzero.

This is the direction that says a random object *does* contain the structure being counted:
when the variance is small next to the squared mean, almost all the weight sits where the
count is nonzero. Taking `w := bweight p` and `N` a subgraph count turns it into the
positive half of a threshold result.

Phrased for an arbitrary `S` on which `N` vanishes rather than for a `filter`, so that no
decidability of real equality is involved at the call site. -/
theorem wsecond_moment (w : Ω → ℝ) (N : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (hmean : 0 < wmean w N) {S : Finset Ω} (hS : ∀ ω ∈ S, N ω = 0) :
    (∑ ω ∈ S, w ω) * (wmean w N) ^ 2 ≤ wvar w N := by
  have hsub : S ⊆ univ.filter fun ω => wmean w N ≤ |N ω - wmean w N| := by
    intro ω hω
    rw [mem_filter]
    refine ⟨mem_univ _, ?_⟩
    rw [hS ω hω, zero_sub, abs_neg, abs_of_pos hmean]
  calc (∑ ω ∈ S, w ω) * (wmean w N) ^ 2
      ≤ (∑ ω ∈ univ.filter fun ω => wmean w N ≤ |N ω - wmean w N|, w ω)
          * (wmean w N) ^ 2 :=
        mul_le_mul_of_nonneg_right
          (Finset.sum_le_sum_of_subset_of_nonneg hsub fun ω _ _ => hw ω) (sq_nonneg _)
    _ ≤ wvar w N := wchebyshev w N hw hmean

end Weighted

section Bernoulli

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The Bernoulli weight of a subset: each element included independently with probability
`p`. With `α := Sym2 V` this is the `G(n, p)` distribution on graphs. -/
def bweight (p : ℝ) (X : Finset α) : ℝ := p ^ #X * (1 - p) ^ (Fintype.card α - #X)

lemma bweight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (X : Finset α) :
    0 ≤ bweight p X :=
  mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)

/-- Over any `S`, the Bernoulli weights relative to `S` total `1`. This is
`Finset.prod_add` with both factors constant. -/
lemma sum_bernoulli_on (S : Finset α) (p : ℝ) :
    ∑ X ∈ S.powerset, p ^ #X * (1 - p) ^ (#S - #X) = 1 := by
  have h := Finset.prod_add (fun _ : α => p) (fun _ : α => 1 - p) S
  calc ∑ X ∈ S.powerset, p ^ #X * (1 - p) ^ (#S - #X)
      = ∑ X ∈ S.powerset, (∏ _i ∈ X, p) * ∏ _i ∈ S \ X, (1 - p) := by
        refine Finset.sum_congr rfl fun X hX => ?_
        rw [mem_powerset] at hX
        rw [prod_const, prod_const, card_sdiff_of_subset hX]
    _ = ∏ _i ∈ S, (p + (1 - p)) := h.symm
    _ = 1 := by simp

/-- The Bernoulli weights total `1`. -/
theorem sum_bweight (p : ℝ) : ∑ X ∈ (univ : Finset α).powerset, bweight p X = 1 := by
  have h := sum_bernoulli_on (univ : Finset α) p
  rwa [card_univ] at h

/-- The subsets avoiding `B` carry weight `(1 - p) ^ #B`. -/
theorem sum_bweight_disjoint (p : ℝ) (B : Finset α) :
    ∑ X ∈ (univ : Finset α).powerset.filter (fun X => Disjoint X B), bweight p X
      = (1 - p) ^ #B := by
  have hset : (univ : Finset α).powerset.filter (fun X => Disjoint X B)
      = (univ \ B).powerset := by
    ext X
    simp only [mem_filter, mem_powerset, subset_univ, true_and, subset_sdiff]
  have hcard : #(univ \ B) = Fintype.card α - #B := by
    rw [card_sdiff_of_subset (subset_univ B), card_univ]
  have hBle : #B ≤ Fintype.card α := by rw [← card_univ]; exact card_le_univ B
  rw [hset]
  calc ∑ X ∈ (univ \ B).powerset, bweight p X
      = ∑ X ∈ (univ \ B).powerset,
          (p ^ #X * (1 - p) ^ (#(univ \ B) - #X)) * (1 - p) ^ #B := by
        refine Finset.sum_congr rfl fun X hX => ?_
        rw [mem_powerset] at hX
        have hXle : #X ≤ #(univ \ B) := card_le_card hX
        rw [bweight, mul_assoc, ← pow_add]
        congr 2
        omega
    _ = (∑ X ∈ (univ \ B).powerset, p ^ #X * (1 - p) ^ (#(univ \ B) - #X)) * (1 - p) ^ #B :=
        (Finset.sum_mul _ _ _).symm
    _ = (1 - p) ^ #B := by rw [sum_bernoulli_on, one_mul]

/-- The subsets containing `B` carry weight `p ^ #B`.

On `α := Sym2 V` this says a fixed set of `#B` edges is present with weight `p ^ #B`, which
is the opening step of every first-moment argument about `G(n, p)`. -/
theorem sum_bweight_superset (p : ℝ) (B : Finset α) :
    ∑ X ∈ (univ : Finset α).powerset.filter (fun X => B ⊆ X), bweight p X = p ^ #B := by
  have hcard : #(univ \ B) = Fintype.card α - #B := by
    rw [card_sdiff_of_subset (subset_univ B), card_univ]
  have hBle : #B ≤ Fintype.card α := by rw [← card_univ]; exact card_le_univ B
  have key : ∑ X ∈ (univ : Finset α).powerset.filter (fun X => B ⊆ X), bweight p X
      = ∑ Y ∈ (univ \ B).powerset,
          p ^ #B * (p ^ #Y * (1 - p) ^ (#(univ \ B) - #Y)) := by
    refine Finset.sum_nbij' (fun X => X \ B) (fun Y => Y ∪ B) ?_ ?_ ?_ ?_ ?_
    · intro X hX
      rw [mem_filter, mem_powerset] at hX
      rw [mem_powerset]
      exact sdiff_subset_sdiff hX.1 Subset.rfl
    · intro Y hY
      rw [mem_powerset] at hY
      rw [mem_filter, mem_powerset]
      exact ⟨subset_univ _, subset_union_right⟩
    · intro X hX
      rw [mem_filter] at hX
      exact sdiff_union_of_subset hX.2
    · intro Y hY
      rw [mem_powerset] at hY
      have hdisj : Disjoint Y B := by
        rw [Finset.disjoint_right]
        intro x hxB hxY
        exact (mem_sdiff.mp (hY hxY)).2 hxB
      rw [union_sdiff_right, sdiff_eq_self_of_disjoint hdisj]
    · intro X hX
      rw [mem_filter, mem_powerset] at hX
      have hBX : B ⊆ X := hX.2
      have hcardX : #(X \ B) + #B = #X := by
        rw [card_sdiff_of_subset hBX]
        have : #B ≤ #X := card_le_card hBX
        omega
      have hexp : Fintype.card α - #X = #(univ \ B) - #(X \ B) := by
        omega
      rw [bweight, hexp, ← hcardX, pow_add]
      ring
  rw [key, ← Finset.mul_sum, sum_bernoulli_on, mul_one]

/-- **The first moment method.**

Let `g i` be a family of "patterns" indexed by `i ∈ I`, each with exactly `m` elements. The
weighted count of patterns contained in a random subset is `#I * p ^ m`.

This is an identity and needs no hypothesis on `p`. Every first-moment argument about
`G(n, p)` is an instance: take `α := Sym2 V`, let `I` index the potential copies of some
fixed subgraph and `g` send each to its edge set, and `m` is that subgraph's edge count.
Note that `g` need not be injective — coincident patterns are counted with multiplicity,
which is what makes this usable without a side condition. -/
theorem sum_bweight_mul_card_filter {ι : Type*} [DecidableEq ι]
    (p : ℝ) (I : Finset ι) (g : ι → Finset α) (m : ℕ) (hm : ∀ i ∈ I, #(g i) = m) :
    ∑ X ∈ (univ : Finset α).powerset, bweight p X * (#(I.filter fun i => g i ⊆ X) : ℝ)
      = #I * p ^ m := by
  classical
  have hcard : ∀ X : Finset α, (#(I.filter fun i => g i ⊆ X) : ℝ)
      = ∑ i ∈ I, (if g i ⊆ X then (1 : ℝ) else 0) := by
    intro X
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : g i ⊆ X <;> simp [h]
  calc ∑ X ∈ (univ : Finset α).powerset, bweight p X * (#(I.filter fun i => g i ⊆ X) : ℝ)
      = ∑ X ∈ (univ : Finset α).powerset, ∑ i ∈ I,
          bweight p X * (if g i ⊆ X then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl fun X _ => ?_
        rw [hcard X, Finset.mul_sum]
    _ = ∑ i ∈ I, ∑ X ∈ (univ : Finset α).powerset,
          bweight p X * (if g i ⊆ X then (1 : ℝ) else 0) := Finset.sum_comm
    _ = ∑ _i ∈ I, p ^ m := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hconv : ∑ X ∈ (univ : Finset α).powerset,
            bweight p X * (if g i ⊆ X then (1 : ℝ) else 0)
              = ∑ X ∈ (univ : Finset α).powerset.filter (fun X => g i ⊆ X), bweight p X := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun X _ => ?_
          by_cases h : g i ⊆ X <;> simp [h]
        rw [hconv, sum_bweight_superset, hm i hi]
    _ = #I * p ^ m := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **The second moment of a pattern count.**

The weighted mean of the square of the number of patterns contained in a random subset is
`∑ i ∈ I, ∑ j ∈ I, p ^ #(g i ∪ g j)`.

The only input beyond the first moment is that `g i ⊆ X` and `g j ⊆ X` together say exactly
`g i ∪ g j ⊆ X`, so `sum_bweight_superset` applies unchanged to the pair. Together with
`sum_bweight_mul_card_filter` and `wchebyshev` this is the second-moment method: the
diagonal terms `i = j` contribute `p ^ #(g i)` and the off-diagonal terms measure how much
patterns overlap. -/
theorem sum_bweight_mul_card_filter_sq {ι : Type*} [DecidableEq ι]
    (p : ℝ) (I : Finset ι) (g : ι → Finset α) :
    ∑ X ∈ (univ : Finset α).powerset, bweight p X * (#(I.filter fun i => g i ⊆ X) : ℝ) ^ 2
      = ∑ i ∈ I, ∑ j ∈ I, p ^ #(g i ∪ g j) := by
  classical
  have hcard : ∀ X : Finset α, (#(I.filter fun i => g i ⊆ X) : ℝ)
      = ∑ i ∈ I, (if g i ⊆ X then (1 : ℝ) else 0) := by
    intro X
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : g i ⊆ X <;> simp [h]
  have hsq : ∀ X : Finset α, (#(I.filter fun i => g i ⊆ X) : ℝ) ^ 2
      = ∑ i ∈ I, ∑ j ∈ I, (if g i ∪ g j ⊆ X then (1 : ℝ) else 0) := by
    intro X
    rw [hcard X, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases hi : g i ⊆ X
    · by_cases hj : g j ⊆ X
      · simp [hi, hj, Finset.union_subset_iff]
      · simp [hi, hj, Finset.union_subset_iff]
    · simp [hi, Finset.union_subset_iff]
  calc ∑ X ∈ (univ : Finset α).powerset,
        bweight p X * (#(I.filter fun i => g i ⊆ X) : ℝ) ^ 2
      = ∑ X ∈ (univ : Finset α).powerset, ∑ i ∈ I, ∑ j ∈ I,
          bweight p X * (if g i ∪ g j ⊆ X then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl fun X _ => ?_
        rw [hsq X, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ i ∈ I, ∑ j ∈ I, ∑ X ∈ (univ : Finset α).powerset,
          bweight p X * (if g i ∪ g j ⊆ X then (1 : ℝ) else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i ∈ I, ∑ j ∈ I, p ^ #(g i ∪ g j) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        have hconv : ∑ X ∈ (univ : Finset α).powerset,
            bweight p X * (if g i ∪ g j ⊆ X then (1 : ℝ) else 0)
              = ∑ X ∈ (univ : Finset α).powerset.filter (fun X => g i ∪ g j ⊆ X),
                bweight p X := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun X _ => ?_
          by_cases h : g i ∪ g j ⊆ X <;> simp [h]
        rw [hconv, sum_bweight_superset]

/-- `wmean` against Bernoulli weights is the sum over the powerset, which is the shape the
first- and second-moment lemmas above produce. `Finset.powerset_univ` is what makes these
the same space: every `Finset α` is a subset of `univ`. -/
lemma wmean_eq_sum_powerset (w : Finset α → ℝ) (N : Finset α → ℝ) :
    wmean w N = ∑ X ∈ (univ : Finset α).powerset, w X * N X := by
  rw [wmean, Finset.powerset_univ]

lemma wvar_eq_sum_powerset (w : Finset α → ℝ) (N : Finset α → ℝ) :
    wvar w N = ∑ X ∈ (univ : Finset α).powerset, w X * (N X - wmean w N) ^ 2 := by
  rw [wvar, Finset.powerset_univ]

end Bernoulli

end PMC
