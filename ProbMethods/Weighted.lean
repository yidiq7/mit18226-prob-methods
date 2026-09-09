import ProbMethods.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Combinatorics.SetFamily.FourFunctions

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
* `PMC.pweight` — the same with a *per-element* probability `p i`, for independent but not
  identically distributed coordinates. `Finset.prod_add` handles this with no extra work,
  since it never needed the factors to be constant; Theorem 5.0.7 and any random graph
  with varying edge probabilities want this form.

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
* `PMC.DeterminedBy` and `PMC.card_inter_mul_of_determinedBy` — the **reusable discharge**
  of the local lemma's independence hypothesis: two events determined by disjoint blocks of
  coordinates satisfy `P(A ∩ A') = P(A) P(A')`, so an application only has to exhibit the
  blocks and check they are disjoint.
* `PMC.card_filter_inter_prod` — **block independence**: properties depending on disjoint
  blocks of coordinates factor, by the bijection `S ↦ (S ∩ C, S ∩ (V \ C))`. This is the
  counting form of independence that every application of the local lemma has to
  discharge.
* `PMC.card_filter_inter` — **restriction**: counting subsets of `V` by a property of
  their intersection with `A ⊆ V` factors as `2 ^ #(V \ A)` times the count over
  `A.powerset`. This is what lifts a bound proved on one hypergraph edge to the space of
  colourings of the whole ground set, where a union bound can be taken.
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

/-- The weight of an *event*, i.e. its probability when the weights total `1`. Events are
`Finset`s of the sample space. -/
def wprob (w : Ω → ℝ) (A : Finset Ω) : ℝ := ∑ ω ∈ A, w ω

lemma wprob_nonneg {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (A : Finset Ω) : 0 ≤ wprob w A :=
  Finset.sum_nonneg fun ω _ => hw ω

lemma wprob_mono {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) {A B : Finset Ω} (h : A ⊆ B) :
    wprob w A ≤ wprob w B :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun ω _ _ => hw ω

@[simp] lemma wprob_empty (w : Ω → ℝ) : wprob w (∅ : Finset Ω) = 0 := by
  simp [wprob]

lemma wprob_univ (w : Ω → ℝ) : wprob w (univ : Finset Ω) = ∑ ω, w ω := rfl

/-- Splitting an event by another: `P(Bᶜ ∩ S) = P(S) - P(B ∩ S)`.

This is the peeling step of the local lemma's induction, and the reason it can be kept
free of division. -/
lemma wprob_compl_inter [DecidableEq Ω] (w : Ω → ℝ) (B S : Finset Ω) :
    wprob w (Bᶜ ∩ S) = wprob w S - wprob w (B ∩ S) := by
  have hdisj : Disjoint (B ∩ S) (Bᶜ ∩ S) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [mem_inter] at hx hx'
    exact (mem_compl.mp hx'.1) hx.1
  have hunion : (B ∩ S) ∪ (Bᶜ ∩ S) = S := by
    ext x
    simp only [mem_union, mem_inter, mem_compl]
    constructor
    · rintro (⟨-, h⟩ | ⟨-, h⟩) <;> exact h
    · intro h
      by_cases hB : x ∈ B
      · exact Or.inl ⟨hB, h⟩
      · exact Or.inr ⟨hB, h⟩
  have h : wprob w (B ∩ S) + wprob w (Bᶜ ∩ S) = wprob w S := by
    rw [wprob, wprob, wprob, ← Finset.sum_union hdisj, hunion]
  linarith

/-- Complement: `P(Aᶜ) = P(univ) - P(A)`. -/
lemma wprob_union_le [DecidableEq Ω] {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (A B : Finset Ω) :
    wprob w (A ∪ B) ≤ wprob w A + wprob w B := by
  classical
  have hdisj : Disjoint A (B \ A) := Finset.disjoint_sdiff
  have hunion : A ∪ B \ A = A ∪ B := by
    ext x
    simp only [mem_union, mem_sdiff]
    tauto
  calc wprob w (A ∪ B) = wprob w A + wprob w (B \ A) := by
        rw [wprob, wprob, wprob, ← Finset.sum_union hdisj, hunion]
    _ ≤ wprob w A + wprob w B := by
        have := wprob_mono hw (Finset.sdiff_subset (s := B) (t := A))
        linarith

lemma wprob_biUnion_le [DecidableEq Ω] {ι : Type*} [DecidableEq ι] {w : Ω → ℝ}
    (hw : ∀ ω, 0 ≤ w ω) (T : Finset ι) (Z : ι → Finset Ω) :
    wprob w (T.biUnion Z) ≤ ∑ j ∈ T, wprob w (Z j) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [wprob]
  | @insert a T ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      exact le_trans (wprob_union_le hw _ _) (by linarith)

/-- If `X` is covered by `Y` together with a finite family, its weight is bounded by the
sum of theirs. This is the union bound, in the shape the Janson argument needs. -/
lemma wprob_le_of_subset_union [DecidableEq Ω] {ι : Type*} [DecidableEq ι] {w : Ω → ℝ}
    (hw : ∀ ω, 0 ≤ w ω) {X Y : Finset Ω} {T : Finset ι} {Z : ι → Finset Ω}
    (h : X ⊆ Y ∪ T.biUnion Z) :
    wprob w X ≤ wprob w Y + ∑ j ∈ T, wprob w (Z j) :=
  le_trans (wprob_mono hw h)
    (le_trans (wprob_union_le hw _ _) (by linarith [wprob_biUnion_le hw T Z]))

lemma wprob_le_one {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω = 1) (A : Finset Ω) :
    wprob w A ≤ 1 := by
  rw [← hsum, ← wprob_univ]
  exact wprob_mono hw (subset_univ A)

lemma wprob_compl [DecidableEq Ω] (w : Ω → ℝ) (A : Finset Ω) :
    wprob w Aᶜ = (∑ ω, w ω) - wprob w A := by
  have h : wprob w A + wprob w Aᶜ = ∑ ω, w ω := by
    rw [wprob, wprob, ← Finset.sum_union (disjoint_compl_right)]
    congr 1
    simp
  linarith

/-- The weighted variance of `X`, taken about its own weighted mean. -/
def wvar (w : Ω → ℝ) (X : Ω → ℝ) : ℝ := ∑ ω, w ω * (X ω - wmean w X) ^ 2

lemma wvar_nonneg {w : Ω → ℝ} (X : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) : 0 ≤ wvar w X :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (hw ω) (sq_nonneg _)

/-- `wvar w X = E[X²] - (E X)²`, when the weights total `1`. This is what turns a second
moment computed by `sum_bweight_mul_card_filter_sq` into a variance. -/
lemma wvar_eq_wmean_sq_sub (w : Ω → ℝ) (X : Ω → ℝ) (hw : ∑ ω, w ω = 1) :
    wvar w X = wmean w (fun ω => X ω ^ 2) - (wmean w X) ^ 2 := by
  have hexp : ∀ ω : Ω, w ω * (X ω - wmean w X) ^ 2
      = w ω * X ω ^ 2 - 2 * wmean w X * (w ω * X ω) + (wmean w X) ^ 2 * w ω := by
    intro ω; ring
  rw [wvar, Finset.sum_congr rfl fun ω _ => hexp ω, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hw]
  simp only [wmean]
  ring

/-- **Chebyshev's inequality** (Zhao, Theorem 4.1.5), over a finite weighted space.

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

/-- **Markov's inequality** over a finite weighted space (Zhao, Theorem 3.3.1).

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

/-- **The second moment method** (Zhao, Corollary 4.1.7, in the form applications use).

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

/-- **Restricting a subset count to a sub-ground-set.**

Counting the subsets of `V` by a property of their intersection with `A ⊆ V`: each
`T ⊆ A` has exactly `2 ^ #(V \ A)` preimages under `S ↦ S ∩ A`, so the count factors.

This is what lets a bound proved over `A.powerset` — a Chernoff bound for a sum over one
hypergraph edge, say — be lifted to the space of colourings of the whole ground set, where
a union bound over several edges can be taken. -/
theorem card_filter_inter (V A : Finset α) (hA : A ⊆ V)
    (P : Finset α → Prop) [DecidablePred P] :
    #(V.powerset.filter fun S => P (S ∩ A))
      = 2 ^ #(V \ A) * #(A.powerset.filter P) := by
  classical
  have hmaps : ∀ S ∈ V.powerset.filter (fun S => P (S ∩ A)),
      S ∩ A ∈ A.powerset.filter P := by
    intro S hS
    rw [mem_filter, mem_powerset] at hS
    rw [mem_filter, mem_powerset]
    exact ⟨inter_subset_right, hS.2⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hfib : ∀ T ∈ A.powerset.filter P,
      #((V.powerset.filter fun S => P (S ∩ A)).filter fun S => S ∩ A = T)
        = 2 ^ #(V \ A) := by
    intro T hT
    rw [mem_filter, mem_powerset] at hT
    rw [← card_powerset]
    refine Finset.card_nbij' (fun S => S \ A) (fun R => R ∪ T) ?_ ?_ ?_ ?_
    · intro S hS
      rw [mem_coe, mem_filter, mem_filter, mem_powerset] at hS
      rw [mem_coe, mem_powerset]
      intro x hx
      rw [mem_sdiff] at hx ⊢
      exact ⟨hS.1.1 hx.1, hx.2⟩
    · intro R hR
      rw [mem_coe, mem_powerset] at hR
      have hRA : R ∩ A = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro x hx
        rw [mem_inter] at hx
        exact (mem_sdiff.mp (hR hx.1)).2 hx.2
      have hinter : (R ∪ T) ∩ A = T := by
        rw [Finset.union_inter_distrib_right, hRA, Finset.empty_union,
          Finset.inter_eq_left.mpr hT.1]
      rw [mem_coe, mem_filter, mem_filter, mem_powerset]
      refine ⟨⟨?_, ?_⟩, hinter⟩
      · exact union_subset (hR.trans sdiff_subset) (hT.1.trans hA)
      · rw [hinter]; exact hT.2
    · intro S hS
      rw [mem_coe, mem_filter, mem_filter] at hS
      rw [← hS.2]
      exact Finset.sdiff_union_inter S A
    · intro R hR
      rw [mem_coe, mem_powerset] at hR
      have hRA : Disjoint R A := by
        rw [Finset.disjoint_right]
        intro x hxA hxR
        exact (mem_sdiff.mp (hR hxR)).2 hxA
      show (R ∪ T) \ A = R
      rw [Finset.union_sdiff_distrib, Finset.sdiff_eq_self_of_disjoint hRA,
        Finset.sdiff_eq_empty_iff_subset.mpr hT.1, Finset.union_empty]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, mul_comm]

/-! ### Independent coordinates with differing probabilities -/

/-- The weight of a subset when element `i` is included with its own probability `p i`,
independently. `PMC.bweight` is the constant case.

`Finset.prod_add` never required the factors to be constant, so this costs nothing beyond
stating it — which is the point: independence *is* the product factorisation. -/
def pweight (p : α → ℝ) (X : Finset α) : ℝ :=
  (∏ i ∈ X, p i) * ∏ i ∈ (univ : Finset α) \ X, (1 - p i)

lemma pweight_nonneg {p : α → ℝ} (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (X : Finset α) : 0 ≤ pweight p X :=
  mul_nonneg
    (Finset.prod_nonneg fun i _ => hp0 i)
    (Finset.prod_nonneg fun i _ => by linarith [hp1 i])

/-- The per-element weights total `1`. -/
theorem sum_pweight (p : α → ℝ) :
    ∑ X ∈ (univ : Finset α).powerset, pweight p X = 1 := by
  have h := Finset.prod_add p (fun i => 1 - p i) (univ : Finset α)
  simp only [pweight]
  calc ∑ X ∈ (univ : Finset α).powerset,
        (∏ i ∈ X, p i) * ∏ i ∈ (univ : Finset α) \ X, (1 - p i)
      = ∏ i ∈ (univ : Finset α), (p i + (1 - p i)) := h.symm
    _ = 1 := by simp

/-- A fixed `B` is contained with weight `∏ i ∈ B, p i` — the first-moment input for
independent coordinates with differing probabilities. -/
theorem sum_pweight_superset (p : α → ℝ) (B : Finset α) :
    ∑ X ∈ (univ : Finset α).powerset.filter (fun X => B ⊆ X), pweight p X
      = ∏ i ∈ B, p i := by
  classical
  have key : ∑ X ∈ (univ : Finset α).powerset.filter (fun X => B ⊆ X), pweight p X
      = ∑ Y ∈ (univ \ B).powerset,
          (∏ i ∈ B, p i) * ((∏ i ∈ Y, p i) * ∏ i ∈ (univ \ B) \ Y, (1 - p i)) := by
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
      show (Y ∪ B) \ B = Y
      rw [Finset.union_sdiff_right, Finset.sdiff_eq_self_of_disjoint hdisj]
    · intro X hX
      rw [mem_filter, mem_powerset] at hX
      have hBX : B ⊆ X := hX.2
      have hsplit : (∏ i ∈ X, p i) = (∏ i ∈ B, p i) * ∏ i ∈ X \ B, p i := by
        rw [← Finset.prod_union (Finset.disjoint_sdiff), Finset.union_sdiff_of_subset hBX]
      have hcompl : (univ : Finset α) \ X = (univ \ B) \ (X \ B) := by
        ext x
        simp only [mem_sdiff]
        constructor
        · intro h
          exact ⟨⟨h.1, fun hxB => h.2 (hBX hxB)⟩, fun hx => h.2 hx.1⟩
        · intro h
          refine ⟨h.1.1, fun hxX => ?_⟩
          by_cases hxB : x ∈ B
          · exact h.1.2 hxB
          · exact h.2 ⟨hxX, hxB⟩
      rw [pweight, hsplit, hcompl]
      ring
  rw [key, ← Finset.mul_sum]
  have hone : ∑ Y ∈ (univ \ B).powerset,
      (∏ i ∈ Y, p i) * ∏ i ∈ (univ \ B) \ Y, (1 - p i) = 1 := by
    have h := Finset.prod_add p (fun i => 1 - p i) ((univ : Finset α) \ B)
    calc ∑ Y ∈ (univ \ B).powerset,
          (∏ i ∈ Y, p i) * ∏ i ∈ (univ \ B) \ Y, (1 - p i)
        = ∏ i ∈ (univ : Finset α) \ B, (p i + (1 - p i)) := h.symm
      _ = 1 := by simp
  rw [hone, mul_one]

/-! ### Linear forms

The mean and variance of `S ↦ ∑ i ∈ S, a i` under `bweight p` — a random subset with each
element kept independently with probability `p`. Both come from `PMC.sum_bweight_superset`
alone: the probability that a given pair of coordinates both survive is `p ^ #{i, j}`, which
is `p` when `i = j` and `p ^ 2` otherwise, and that single case split is the whole content
of the variance.
-/

/-- The chance a given coordinate survives is `p`. -/
lemma sum_bweight_mem (p : ℝ) (i : α) :
    ∑ S ∈ (univ : Finset (Finset α)).filter (fun S => i ∈ S), bweight p S = p := by
  have h := sum_bweight_superset p {i}
  rw [Finset.powerset_univ, Finset.card_singleton, pow_one] at h
  have hset : (univ : Finset (Finset α)).filter (fun S => i ∈ S)
      = (univ : Finset (Finset α)).filter (fun X => {i} ⊆ X) := by
    ext S
    simp [Finset.singleton_subset_iff]
  rw [hset]
  exact h

/-- The chance two given coordinates both survive is `p ^ #{i, j}` — the whole content of
the variance computation is that this exponent is `1` when `i = j` and `2` otherwise. -/
lemma sum_bweight_mem_pair (p : ℝ) (i j : α) :
    ∑ S ∈ (univ : Finset (Finset α)).filter (fun S => i ∈ S ∧ j ∈ S), bweight p S
      = p ^ #({i, j} : Finset α) := by
  have h := sum_bweight_superset p {i, j}
  rw [Finset.powerset_univ] at h
  have hset : (univ : Finset (Finset α)).filter (fun S => i ∈ S ∧ j ∈ S)
      = (univ : Finset (Finset α)).filter (fun X => {i, j} ⊆ X) := by
    ext S
    simp [Finset.insert_subset_iff, Finset.singleton_subset_iff]
  rw [hset]
  exact h

/-- Pull a sum over `S` out into a sum over the whole ground set. -/
private lemma sum_over_subset (S : Finset α) (f : α → ℝ) :
    ∑ i ∈ S, f i = ∑ i : α, (if i ∈ S then f i else 0) := by
  rw [← Finset.sum_filter]
  exact Finset.sum_congr (by ext i; simp) fun _ _ => rfl

/-- **The mean of a linear form** under `bweight p`. -/
theorem wmean_bweight_linear (p : ℝ) (a : α → ℝ) :
    wmean (bweight p) (fun S => ∑ i ∈ S, a i) = p * ∑ i, a i := by
  classical
  calc wmean (bweight p) (fun S => ∑ i ∈ S, a i)
      = ∑ S : Finset α, ∑ i : α, (if i ∈ S then bweight p S * a i else 0) := by
        refine Finset.sum_congr rfl fun S _ => ?_
        show bweight p S * ∑ i ∈ S, a i = _
        rw [Finset.mul_sum, sum_over_subset]
    _ = ∑ i : α, ∑ S : Finset α, (if i ∈ S then bweight p S * a i else 0) := by
        rw [Finset.sum_comm]
    _ = ∑ i : α, a i * p := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_filter]
        calc ∑ S ∈ (univ : Finset (Finset α)).filter (fun S => i ∈ S), bweight p S * a i
            = (∑ S ∈ (univ : Finset (Finset α)).filter (fun S => i ∈ S), bweight p S)
              * a i := (Finset.sum_mul ..).symm
          _ = a i * p := by rw [sum_bweight_mem]; ring
    _ = p * ∑ i, a i := by rw [← Finset.sum_mul]; ring

/-- **The variance of a linear form** under `bweight p`: `p (1 - p) ∑ a i ^ 2`.

The coordinates are independent, so the variances add — but nothing here appeals to a
general independence lemma; it all falls out of `PMC.sum_bweight_mem_pair` and the fact that
`#{i, j}` is `1` exactly when `i = j`. -/
theorem wvar_bweight_linear (p : ℝ) (a : α → ℝ) :
    wvar (bweight p) (fun S => ∑ i ∈ S, a i) = p * (1 - p) * ∑ i, a i ^ 2 := by
  classical
  have hsum : ∑ S : Finset α, bweight p S = 1 := by
    have h := sum_bweight (α := α) p
    rwa [Finset.powerset_univ] at h
  have hsq : wmean (bweight p) (fun S => (∑ i ∈ S, a i) ^ 2)
      = ∑ i : α, ∑ j : α, a i * a j * p ^ #({i, j} : Finset α) := by
    calc wmean (bweight p) (fun S => (∑ i ∈ S, a i) ^ 2)
        = ∑ S : Finset α, ∑ i : α, ∑ j : α,
            (if i ∈ S ∧ j ∈ S then bweight p S * (a i * a j) else 0) := by
          refine Finset.sum_congr rfl fun S _ => ?_
          show bweight p S * (∑ i ∈ S, a i) ^ 2 = _
          rw [sq, Finset.sum_mul_sum, Finset.mul_sum, sum_over_subset]
          refine Finset.sum_congr rfl fun i _ => ?_
          by_cases hi : i ∈ S
          · rw [if_pos hi, Finset.mul_sum, sum_over_subset]
            refine Finset.sum_congr rfl fun j _ => ?_
            by_cases hj : j ∈ S
            · simp [hi, hj, mul_assoc]
            · simp [hj]
          · rw [if_neg hi]
            refine (Finset.sum_eq_zero fun j _ => ?_).symm
            simp [hi]
      _ = ∑ i : α, ∑ j : α, ∑ S : Finset α,
            (if i ∈ S ∧ j ∈ S then bweight p S * (a i * a j) else 0) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ i : α, ∑ j : α, a i * a j * p ^ #({i, j} : Finset α) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [← Finset.sum_filter]
          calc ∑ S ∈ (univ : Finset (Finset α)).filter (fun S => i ∈ S ∧ j ∈ S),
                bweight p S * (a i * a j)
              = (∑ S ∈ (univ : Finset (Finset α)).filter (fun S => i ∈ S ∧ j ∈ S),
                  bweight p S) * (a i * a j) := (Finset.sum_mul ..).symm
            _ = a i * a j * p ^ #({i, j} : Finset α) := by
                rw [sum_bweight_mem_pair]; ring
  have hdiag : ∀ i : α, #({i, i} : Finset α) = 1 := fun i => by simp
  have hoff : ∀ i j : α, i ≠ j → #({i, j} : Finset α) = 2 := fun _ _ hij =>
    Finset.card_pair hij
  have hsplit : ∑ i : α, ∑ j : α, a i * a j * p ^ #({i, j} : Finset α)
      = p * ∑ i : α, a i ^ 2 + p ^ 2 * ((∑ i, a i) ^ 2 - ∑ i, a i ^ 2) := by
    have hrow : ∀ i : α, ∑ j : α, a i * a j * p ^ #({i, j} : Finset α)
        = a i ^ 2 * p + p ^ 2 * (a i * (∑ j, a j) - a i ^ 2) := by
      intro i
      have h1 : ∀ j : α, a i * a j * p ^ #({i, j} : Finset α)
          = p ^ 2 * (a i * a j) + (if j = i then a i ^ 2 * p - p ^ 2 * a i ^ 2 else 0) := by
        intro j
        by_cases hj : j = i
        · subst hj
          rw [if_pos rfl, hdiag j]
          ring
        · rw [if_neg hj, hoff i j (Ne.symm hj)]
          ring
      rw [Finset.sum_congr rfl fun j _ => h1 j, Finset.sum_add_distrib,
        Finset.sum_ite_eq' univ i (fun _ => a i ^ 2 * p - p ^ 2 * a i ^ 2),
        if_pos (mem_univ i), ← Finset.mul_sum, ← Finset.mul_sum]
      ring
    rw [Finset.sum_congr rfl fun i _ => hrow i, Finset.sum_add_distrib, ← Finset.sum_mul,
      ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_mul]
    ring
  rw [wvar_eq_wmean_sq_sub _ _ hsum, hsq, hsplit, wmean_bweight_linear]
  ring

/-- **The Chapter 4 weight is the Chapter 7 weight at a constant probability.**

`PMC.bweight` (used for `G(n, p)` and the second-moment results) is `PMC.pweight` at the
constant function. Without this bridge the two halves of the library cannot be combined:
FKG, Harris and Janson are all stated for `pweight`, while the variance computations are
stated for `bweight`. -/
theorem bweight_eq_pweight (p : ℝ) (X : Finset α) :
    bweight p X = pweight (fun _ => p) X := by
  rw [bweight, pweight, Finset.prod_const, Finset.prod_const,
    card_sdiff_of_subset (subset_univ X), card_univ]

/-- `pweight` as a single product over the ground set. -/
lemma pweight_eq_prod (p : α → ℝ) (T : Finset α) :
    pweight p T = ∏ i : α, (if i ∈ T then p i else 1 - p i) := by
  classical
  rw [pweight, Finset.prod_ite]
  congr 1
  · congr 1
    ext i
    simp
  · congr 1
    ext i
    simp [mem_sdiff]

/-- **Product weights are log-modular**: `w T * w U = w (T ∩ U) * w (T ∪ U)`, with
*equality*.

This is exactly the hypothesis Mathlib's `fkg` needs (it asks only for `≤`), and it holds
with equality precisely because the coordinates are independent. -/
lemma pweight_mul_pweight (p : α → ℝ) (T U : Finset α) :
    pweight p T * pweight p U = pweight p (T ∩ U) * pweight p (T ∪ U) := by
  classical
  rw [pweight_eq_prod, pweight_eq_prod, pweight_eq_prod, pweight_eq_prod,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hT : i ∈ T <;> by_cases hU : i ∈ U <;>
    simp [hT, hU, mem_inter, mem_union] <;> ring

/-- **The Harris–FKG inequality** for independent coordinates (Zhao, Theorem 7.1.5).

Two monotone increasing nonnegative functions are positively correlated under a product
measure: `E[f] * E[g] ≤ E[f * g]`.

**Mathlib proves the general FKG inequality** (`fkg`, in
`Mathlib/Combinatorics/SetFamily/FourFunctions.lean`) for any log-supermodular measure on a
distributive lattice, via the Ahlswede–Daykin four functions theorem. All this does is
supply the log-supermodularity — which for a product measure holds with equality — and
normalise by `∑ w = 1`. Zhao's §7.1 is therefore upstream, not work. -/
theorem pweight_fkg (p : α → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    {f g : Finset α → ℝ} (hf0 : 0 ≤ f) (hg0 : 0 ≤ g)
    (hf : Monotone f) (hg : Monotone g) :
    wmean (pweight p) f * wmean (pweight p) g
      ≤ wmean (pweight p) (fun T => f T * g T) := by
  classical
  have hw0 : (0 : Finset α → ℝ) ≤ pweight p := fun T => pweight_nonneg hp0 hp1 T
  have hwsum : ∑ T : Finset α, pweight p T = 1 := by
    have h := sum_pweight (α := α) p
    rwa [Finset.powerset_univ] at h
  have h := fkg (μ := pweight p) (f := f) (g := g) hw0 hf0 hg0 hf hg
    (fun T U => le_of_eq (pweight_mul_pweight p T U))
  rw [hwsum, one_mul] at h
  simpa only [wmean] using h

/-- **Harris' inequality, decreasing form** (Zhao, Corollary 7.1.6(a)). The same statement
for *antitone* `f` and `g`.

`Finset α` and its order dual are both distributive lattices, and the log-supermodularity
`pweight p T * pweight p U = pweight p (T ∩ U) * pweight p (T ∪ U)` is symmetric in `⊓`
and `⊔`, so the FKG hypotheses transport to the dual verbatim — where `Monotone` means
`Antitone`. Decreasing events are what Janson's inequality needs. -/
theorem pweight_fkg_anti (p : α → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    {f g : Finset α → ℝ} (hf0 : 0 ≤ f) (hg0 : 0 ≤ g)
    (hf : Antitone f) (hg : Antitone g) :
    wmean (pweight p) f * wmean (pweight p) g
      ≤ wmean (pweight p) (fun T => f T * g T) := by
  classical
  have hw0 : (0 : (Finset α)ᵒᵈ → ℝ) ≤ fun T => pweight p (OrderDual.ofDual T) :=
    fun T => pweight_nonneg hp0 hp1 _
  have hwsum : ∑ T : (Finset α)ᵒᵈ, pweight p (OrderDual.ofDual T) = 1 := by
    have h := sum_pweight (α := α) p
    rwa [Finset.powerset_univ] at h
  have h := fkg (μ := fun T : (Finset α)ᵒᵈ => pweight p (OrderDual.ofDual T))
    (f := fun T : (Finset α)ᵒᵈ => f (OrderDual.ofDual T))
    (g := fun T : (Finset α)ᵒᵈ => g (OrderDual.ofDual T))
    hw0 (fun T => hf0 _) (fun T => hg0 _) (fun a b hab => hf hab) (fun a b hab => hg hab)
    (fun a b => le_of_eq (by
      simpa [mul_comm] using pweight_mul_pweight p (OrderDual.ofDual a) (OrderDual.ofDual b)))
  rw [hwsum, one_mul] at h
  exact h

/-- **Events on disjoint blocks of coordinates factor.**

If one property depends only on `S ∩ C` and another only on `S ∩ (V \ C)`, the subsets of
`V` satisfying both are counted by the product of the two separate counts. The bijection is
`S ↦ (S ∩ C, S ∩ (V \ C))`.

This is the counting form of independence for events determined by disjoint sets of
coordinates — the hypothesis every application of the local lemma has to discharge. -/
theorem card_filter_inter_prod (V C : Finset α) (hC : C ⊆ V)
    (P Q : Finset α → Prop) [DecidablePred P] [DecidablePred Q] :
    #(V.powerset.filter fun S => P (S ∩ C) ∧ Q (S ∩ (V \ C)))
      = #(C.powerset.filter P) * #((V \ C).powerset.filter Q) := by
  classical
  rw [← card_product]
  refine Finset.card_nbij' (fun S => (S ∩ C, S ∩ (V \ C)))
    (fun q => q.1 ∪ q.2) ?_ ?_ ?_ ?_
  · intro S hS
    rw [mem_coe, mem_filter, mem_powerset] at hS
    rw [mem_coe, mem_product, mem_filter, mem_filter, mem_powerset, mem_powerset]
    exact ⟨⟨inter_subset_right, hS.2.1⟩, ⟨inter_subset_right, hS.2.2⟩⟩
  · intro q hq
    rw [mem_coe, mem_product, mem_filter, mem_filter, mem_powerset, mem_powerset] at hq
    obtain ⟨⟨hq1, hP⟩, ⟨hq2, hQ⟩⟩ := hq
    have hdisj : Disjoint q.2 C := by
      rw [Finset.disjoint_left]
      intro x hx hxC
      exact (mem_sdiff.mp (hq2 hx)).2 hxC
    have h1 : (q.1 ∪ q.2) ∩ C = q.1 := by
      rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hq1,
        Finset.disjoint_iff_inter_eq_empty.mp hdisj, Finset.union_empty]
    have hdisj2 : Disjoint q.1 (V \ C) := by
      rw [Finset.disjoint_left]
      intro x hx hxV
      exact (mem_sdiff.mp hxV).2 (hq1 hx)
    have h2 : (q.1 ∪ q.2) ∩ (V \ C) = q.2 := by
      rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hq2,
        Finset.disjoint_iff_inter_eq_empty.mp hdisj2, Finset.empty_union]
    rw [mem_coe, mem_filter, mem_powerset]
    refine ⟨union_subset (hq1.trans hC) (hq2.trans sdiff_subset), ?_, ?_⟩
    · rw [h1]; exact hP
    · rw [h2]; exact hQ
  · intro S hS
    rw [mem_coe, mem_filter, mem_powerset] at hS
    show S ∩ C ∪ S ∩ (V \ C) = S
    rw [← Finset.inter_union_distrib_left, Finset.union_sdiff_of_subset hC,
      Finset.inter_eq_left.mpr hS.1]
  · intro q hq
    rw [mem_coe, mem_product, mem_filter, mem_filter, mem_powerset, mem_powerset] at hq
    obtain ⟨⟨hq1, -⟩, ⟨hq2, -⟩⟩ := hq
    have hdisj : Disjoint q.2 C := by
      rw [Finset.disjoint_left]
      intro x hx hxC
      exact (mem_sdiff.mp (hq2 hx)).2 hxC
    have hdisj2 : Disjoint q.1 (V \ C) := by
      rw [Finset.disjoint_left]
      intro x hx hxV
      exact (mem_sdiff.mp hxV).2 (hq1 hx)
    show ((q.1 ∪ q.2) ∩ C, (q.1 ∪ q.2) ∩ (V \ C)) = q
    rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hq1,
      Finset.disjoint_iff_inter_eq_empty.mp hdisj, Finset.union_empty,
      Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hq2,
      Finset.disjoint_iff_inter_eq_empty.mp hdisj2, Finset.empty_union]

/-! ### Block independence for `pweight`

`PMC.card_inter_mul_of_determinedBy` gives independence of events on disjoint coordinate
blocks for the *uniform* weight. The same is true for `pweight`, and the applications need
it: Janson's upper bound conditions on the bad sets that share no element with the current
one, which is exactly an event on the complementary block.
-/

/-- The weight of one *block* of coordinates: only the coordinates in `D` are decided.
`PMC.pweight` is the case `D = univ`. -/
def pweightOn (D : Finset α) (p : α → ℝ) (T : Finset α) : ℝ :=
  (∏ i ∈ T, p i) * ∏ i ∈ D \ T, (1 - p i)

@[simp] lemma pweightOn_univ (p : α → ℝ) (S : Finset α) :
    pweightOn univ p S = pweight p S := rfl

/-- A block's weights total `1`, by `Finset.prod_add` again. -/
theorem sum_pweightOn (D : Finset α) (p : α → ℝ) :
    ∑ T ∈ D.powerset, pweightOn D p T = 1 := by
  have h := Finset.prod_add p (fun i => 1 - p i) D
  rw [show ∑ T ∈ D.powerset, pweightOn D p T
      = ∑ T ∈ D.powerset, (∏ i ∈ T, p i) * ∏ i ∈ D \ T, (1 - p i) from rfl, ← h]
  simp

lemma pweightOn_nonneg {p : α → ℝ} (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (D T : Finset α) :
    0 ≤ pweightOn D p T :=
  mul_nonneg (Finset.prod_nonneg fun i _ => hp0 i)
    (Finset.prod_nonneg fun i _ => by linarith [hp1 i])

/-- **The two blocks' weights multiply to the whole weight.** -/
theorem pweightOn_mul_pweightOn (p : α → ℝ) (C S : Finset α) :
    pweightOn C p (S ∩ C) * pweightOn ((univ : Finset α) \ C) p (S ∩ ((univ : Finset α) \ C))
      = pweight p S := by
  classical
  have hdisj1 : Disjoint (S ∩ C) (S ∩ ((univ : Finset α) \ C)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact (mem_sdiff.mp (mem_inter.mp hx').2).2 (mem_inter.mp hx).2
  have hunion1 : S ∩ C ∪ S ∩ ((univ : Finset α) \ C) = S := by
    ext x
    simp only [mem_union, mem_inter, mem_sdiff, mem_univ, true_and]
    tauto
  have hdisj2 : Disjoint (C \ (S ∩ C))
      (((univ : Finset α) \ C) \ (S ∩ ((univ : Finset α) \ C))) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact (mem_sdiff.mp (mem_sdiff.mp hx').1).2 (mem_sdiff.mp hx).1
  have hunion2 : C \ (S ∩ C) ∪ ((univ : Finset α) \ C) \ (S ∩ ((univ : Finset α) \ C))
      = (univ : Finset α) \ S := by
    ext x
    simp only [mem_union, mem_sdiff, mem_inter, mem_univ, true_and]
    tauto
  rw [pweightOn, pweightOn, pweight]
  calc (∏ i ∈ S ∩ C, p i) * (∏ i ∈ C \ (S ∩ C), (1 - p i))
        * ((∏ i ∈ S ∩ ((univ : Finset α) \ C), p i)
          * ∏ i ∈ ((univ : Finset α) \ C) \ (S ∩ ((univ : Finset α) \ C)), (1 - p i))
      = ((∏ i ∈ S ∩ C, p i) * ∏ i ∈ S ∩ ((univ : Finset α) \ C), p i)
        * ((∏ i ∈ C \ (S ∩ C), (1 - p i))
          * ∏ i ∈ ((univ : Finset α) \ C) \ (S ∩ ((univ : Finset α) \ C)), (1 - p i)) := by
        ring
    _ = (∏ i ∈ S, p i) * ∏ i ∈ (univ : Finset α) \ S, (1 - p i) := by
        rw [← Finset.prod_union hdisj1, ← Finset.prod_union hdisj2, hunion1, hunion2]

/-- **The weighted analogue of `PMC.card_filter_inter_prod`.**

A condition on the trace in `C` and a condition on the trace outside `C` are independent:
the total weight factors as the product of the two block weights. -/
theorem sum_pweight_filter_split (p : α → ℝ) (C : Finset α)
    (P Q : Finset α → Prop) [DecidablePred P] [DecidablePred Q] :
    ∑ S ∈ (univ : Finset (Finset α)).filter
        (fun S => P (S ∩ C) ∧ Q (S ∩ ((univ : Finset α) \ C))), pweight p S
      = (∑ T ∈ C.powerset.filter P, pweightOn C p T)
        * ∑ U ∈ ((univ : Finset α) \ C).powerset.filter Q,
            pweightOn ((univ : Finset α) \ C) p U := by
  classical
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_nbij' (fun S => (S ∩ C, S ∩ ((univ : Finset α) \ C)))
    (fun q => q.1 ∪ q.2) ?_ ?_ ?_ ?_ ?_
  · intro S hS
    rw [mem_filter] at hS
    rw [Finset.mem_product, mem_filter, mem_filter, mem_powerset, mem_powerset]
    exact ⟨⟨inter_subset_right, hS.2.1⟩, ⟨inter_subset_right, hS.2.2⟩⟩
  · intro q hq
    rw [Finset.mem_product, mem_filter, mem_filter, mem_powerset, mem_powerset] at hq
    obtain ⟨⟨hq1, hP⟩, ⟨hq2, hQ⟩⟩ := hq
    have hdisj : Disjoint q.2 C := by
      rw [Finset.disjoint_left]
      intro x hx hxC
      exact (mem_sdiff.mp (hq2 hx)).2 hxC
    have hdisj2 : Disjoint q.1 ((univ : Finset α) \ C) := by
      rw [Finset.disjoint_left]
      intro x hx hxV
      exact (mem_sdiff.mp hxV).2 (hq1 hx)
    have h1 : (q.1 ∪ q.2) ∩ C = q.1 := by
      rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hq1,
        Finset.disjoint_iff_inter_eq_empty.mp hdisj, Finset.union_empty]
    have h2 : (q.1 ∪ q.2) ∩ ((univ : Finset α) \ C) = q.2 := by
      rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hq2,
        Finset.disjoint_iff_inter_eq_empty.mp hdisj2, Finset.empty_union]
    rw [mem_filter]
    exact ⟨mem_univ _, by rw [h1]; exact hP, by rw [h2]; exact hQ⟩
  · intro S _
    show S ∩ C ∪ S ∩ ((univ : Finset α) \ C) = S
    ext x
    simp only [mem_union, mem_inter, mem_sdiff, mem_univ, true_and]
    tauto
  · intro q hq
    rw [Finset.mem_product, mem_filter, mem_filter, mem_powerset, mem_powerset] at hq
    obtain ⟨⟨hq1, -⟩, ⟨hq2, -⟩⟩ := hq
    have hdisj : Disjoint q.2 C := by
      rw [Finset.disjoint_left]
      intro x hx hxC
      exact (mem_sdiff.mp (hq2 hx)).2 hxC
    have hdisj2 : Disjoint q.1 ((univ : Finset α) \ C) := by
      rw [Finset.disjoint_left]
      intro x hx hxV
      exact (mem_sdiff.mp hxV).2 (hq1 hx)
    show ((q.1 ∪ q.2) ∩ C, (q.1 ∪ q.2) ∩ ((univ : Finset α) \ C)) = q
    rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hq1,
      Finset.disjoint_iff_inter_eq_empty.mp hdisj, Finset.union_empty,
      Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hq2,
      Finset.disjoint_iff_inter_eq_empty.mp hdisj2, Finset.empty_union]
  · intro S _
    exact (pweightOn_mul_pweightOn p C S).symm

/-! ### Events determined by a block of coordinates -/

/-- An event is *determined by* `C` when membership depends only on the intersection with
`C`. -/
def DeterminedBy (C : Finset α) (A : Finset (Finset α)) : Prop :=
  ∀ S T : Finset α, S ∩ C = T ∩ C → (S ∈ A ↔ T ∈ A)

lemma DeterminedBy.mem_iff {C : Finset α} {A : Finset (Finset α)} (hA : DeterminedBy C A)
    (S : Finset α) : S ∈ A ↔ S ∩ C ∈ A := by
  refine hA S (S ∩ C) ?_
  rw [Finset.inter_assoc, Finset.inter_self]

/-- The count of an event determined by `C`, in terms of its trace on `C`. -/
lemma DeterminedBy.card_eq {C : Finset α} {A : Finset (Finset α)} (hA : DeterminedBy C A) :
    #A = 2 ^ #((univ : Finset α) \ C) * #(C.powerset.filter fun U => U ∈ A) := by
  classical
  have hrw : A = (univ : Finset α).powerset.filter fun S => S ∩ C ∈ A := by
    ext S
    rw [mem_filter, mem_powerset]
    exact ⟨fun h => ⟨subset_univ S, (hA.mem_iff S).mp h⟩,
      fun h => (hA.mem_iff S).mpr h.2⟩
  calc #A = #((univ : Finset α).powerset.filter fun S => S ∩ C ∈ A) := by rw [← hrw]
    _ = 2 ^ #((univ : Finset α) \ C) * #(C.powerset.filter fun U => U ∈ A) :=
        card_filter_inter (univ : Finset α) C (subset_univ C) (fun U => U ∈ A)

/-- Determinacy is monotone in the block. -/
lemma DeterminedBy.mono {C C' : Finset α} {A : Finset (Finset α)} (h : C ⊆ C')
    (hA : DeterminedBy C A) : DeterminedBy C' A := by
  intro S T hST
  refine hA S T ?_
  have hS : S ∩ C = (S ∩ C') ∩ C := by
    rw [Finset.inter_assoc, Finset.inter_eq_right.mpr h]
  have hT : T ∩ C = (T ∩ C') ∩ C := by
    rw [Finset.inter_assoc, Finset.inter_eq_right.mpr h]
  rw [hS, hT, hST]

lemma DeterminedBy.inter {C : Finset α} {A B : Finset (Finset α)}
    (hA : DeterminedBy C A) (hB : DeterminedBy C B) : DeterminedBy C (A ∩ B) := by
  intro S T hST
  rw [mem_inter, mem_inter, hA S T hST, hB S T hST]

lemma DeterminedBy.compl {C : Finset α} {A : Finset (Finset α)} (hA : DeterminedBy C A) :
    DeterminedBy C Aᶜ := by
  intro S T hST
  rw [mem_compl, mem_compl, hA S T hST]

/-- **Events determined by disjoint blocks are independent, for `pweight`.**

The non-uniform analogue of `PMC.card_inter_mul_of_determinedBy`. An application only has
to exhibit the blocks and check they are disjoint. -/
theorem sum_pweight_inter_of_determinedBy (p : α → ℝ) {C : Finset α}
    {A B : Finset (Finset α)} (hA : DeterminedBy C A)
    (hB : DeterminedBy ((univ : Finset α) \ C) B) :
    (∑ S ∈ A ∩ B, pweight p S) = (∑ S ∈ A, pweight p S) * ∑ S ∈ B, pweight p S := by
  classical
  have hfullC : ((univ : Finset α) \ C).powerset.filter (fun _ => True)
      = ((univ : Finset α) \ C).powerset := Finset.filter_true_of_mem fun _ _ => trivial
  have hfullD : C.powerset.filter (fun _ => True) = C.powerset :=
    Finset.filter_true_of_mem fun _ _ => trivial
  have hAsum : (∑ S ∈ A, pweight p S)
      = ∑ T ∈ C.powerset.filter (fun T => T ∈ A), pweightOn C p T := by
    have h := sum_pweight_filter_split p C (fun T => T ∈ A) (fun _ => True)
    rw [hfullC, sum_pweightOn, mul_one] at h
    rw [← h]
    exact Finset.sum_congr (by ext S; simp [hA.mem_iff S]) fun _ _ => rfl
  have hBsum : (∑ S ∈ B, pweight p S)
      = ∑ U ∈ ((univ : Finset α) \ C).powerset.filter (fun U => U ∈ B),
          pweightOn ((univ : Finset α) \ C) p U := by
    have h := sum_pweight_filter_split p C (fun _ => True) (fun U => U ∈ B)
    rw [hfullD, sum_pweightOn, one_mul] at h
    rw [← h]
    exact Finset.sum_congr (by ext S; simp [hB.mem_iff S]) fun _ _ => rfl
  have hABsum : (∑ S ∈ A ∩ B, pweight p S)
      = (∑ T ∈ C.powerset.filter (fun T => T ∈ A), pweightOn C p T)
        * ∑ U ∈ ((univ : Finset α) \ C).powerset.filter (fun U => U ∈ B),
            pweightOn ((univ : Finset α) \ C) p U := by
    rw [← sum_pweight_filter_split p C (fun T => T ∈ A) (fun U => U ∈ B)]
    exact Finset.sum_congr (by ext S; simp [hA.mem_iff S, hB.mem_iff S]) fun _ _ => rfl
  rw [hABsum, hAsum, hBsum]

@[simp] lemma determinedBy_univ (C : Finset α) :
    DeterminedBy C (univ : Finset (Finset α)) := by
  intro S T _
  simp

/-- **Events determined by disjoint blocks are independent** (in counting form).

`#(A ∩ A') * 2 ^ n = #A * #A'`, i.e. `P(A ∩ A') = P(A) P(A')` under the uniform measure.
This is the reusable discharge of the local lemma's independence hypothesis: an application
only has to exhibit the blocks and check they are disjoint. -/
theorem card_inter_mul_of_determinedBy {C : Finset α} {A A' : Finset (Finset α)}
    (hA : DeterminedBy C A) (hA' : DeterminedBy ((univ : Finset α) \ C) A') :
    #(A ∩ A') * 2 ^ Fintype.card α = #A * #A' := by
  classical
  have hCle : #C ≤ Fintype.card α := by
    rw [← card_univ]; exact card_le_univ C
  have hsdiff : #((univ : Finset α) \ C) = Fintype.card α - #C := by
    rw [card_sdiff_of_subset (subset_univ C), card_univ]
  have hboth : A ∩ A'
      = (univ : Finset α).powerset.filter
        fun S => (S ∩ C ∈ A) ∧ (S ∩ ((univ : Finset α) \ C) ∈ A') := by
    ext S
    rw [mem_inter, mem_filter, mem_powerset]
    exact ⟨fun h => ⟨subset_univ S, (hA.mem_iff S).mp h.1, (hA'.mem_iff S).mp h.2⟩,
      fun h => ⟨(hA.mem_iff S).mpr h.2.1, (hA'.mem_iff S).mpr h.2.2⟩⟩
  rw [hboth, card_filter_inter_prod (univ : Finset α) C (subset_univ C),
    hA.card_eq, hA'.card_eq]
  have hswap : (univ : Finset α) \ ((univ : Finset α) \ C) = C := by
    ext a
    simp only [mem_sdiff, mem_univ, true_and, not_not, and_true]
  rw [hswap, hsdiff]
  have hpow : (2 : ℕ) ^ (Fintype.card α - #C) * 2 ^ #C = 2 ^ Fintype.card α := by
    rw [← pow_add, Nat.sub_add_cancel hCle]
  rw [← hpow]
  ring

end Bernoulli


/-! ### Some point is at most the average

The probabilistic method's core move, in weighted form. -/

/-- **Some point is at most the average.** If the weights are nonnegative and total `1`, some
point has value at most the weighted mean — the averaging step every application of the
probabilistic method makes. -/
theorem exists_le_wmean {Ω : Type*} [Fintype Ω] {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (hsum : ∑ ω, w ω = 1) (f : Ω → ℝ) : ∃ ω, f ω ≤ wmean w f := by
  by_contra hcon
  push_neg at hcon
  -- some weight is positive, since they total `1`
  obtain ⟨ω₀, -, hω₀⟩ : ∃ ω ∈ (univ : Finset Ω), 0 < w ω := by
    by_contra hall
    push_neg at hall
    have : ∑ ω, w ω = 0 :=
      Finset.sum_eq_zero fun ω hω => le_antisymm (hall ω hω) (hw ω)
    rw [this] at hsum
    exact zero_ne_one hsum
  have hlt : ∑ ω, w ω * wmean w f < ∑ ω, w ω * f ω := by
    refine Finset.sum_lt_sum (fun ω _ => ?_) ⟨ω₀, mem_univ _, ?_⟩
    · exact mul_le_mul_of_nonneg_left (le_of_lt (hcon ω)) (hw ω)
    · exact mul_lt_mul_of_pos_left (hcon ω₀) hω₀
  rw [← Finset.sum_mul, hsum, one_mul] at hlt
  exact absurd hlt (lt_irrefl (wmean w f))

/-- **Some point is at least the average**, the other half of the same move. -/
theorem exists_wmean_le {Ω : Type*} [Fintype Ω] {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (hsum : ∑ ω, w ω = 1) (f : Ω → ℝ) : ∃ ω, wmean w f ≤ f ω := by
  obtain ⟨ω, hω⟩ := exists_le_wmean hw hsum (fun ω => -f ω)
  refine ⟨ω, ?_⟩
  have hneg : wmean w (fun ω => -f ω) = -wmean w f := by
    rw [wmean, wmean, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun ω _ => by ring
  rw [hneg] at hω
  linarith

end PMC
