import ProbMethods.Chapter10.CondSupport
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Conditionally independent copies

Several of Chapter 10's entropy arguments use a device the notes describe in words: given a
distribution on `(X, Y)`, *"let `X'` be a conditionally independent copy of `X` given `Y`"*.
It appears in the entropy proof of Theorem 10.3.6 (`K₂,₂`), in Theorem 10.3.7, and — with `d`
copies rather than two — in the bipartite case of Kahn–Zhao (Theorem 10.4.12), where it is
what turns `H(X_A) + d·H(Y|X_A)` into the entropy of a *single* random variable.

This file builds the construction. On `Fin d → Ω`, put

    condProd d w Y f = (∏ i, w (f i)) / P(Y = c)^{d-1}   if every `Y (f i)` equals `c`,
                       0                                  otherwise.

The normalisation is the point: summing over the tuples lying over a fixed `c` gives
`P(c)^d`, so dividing by `P(c)^{d-1}` leaves `P(c)`, and summing over `c` gives `1`
(`PMC.sum_condProd`). Each coordinate then has the original law (`PMC.condProd_marginal`),
and the coordinates are conditionally independent given `Y` by construction.

`d = 0` is excluded: with no copies there is nothing to normalise. The zero-probability
fibres need no special case — Lean's `0 / 0 = 0` makes them contribute nothing on both sides,
which is the same convention that lets `PMC.wentropy_chain` hold without a side condition.
-/

open Finset

namespace PMC

section CondCopies

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
variable {γ : Type*} [Fintype γ] [DecidableEq γ]

/-- The tuples all of whose coordinates lie over the same value of `Y`. -/
def fibreTuples (d : ℕ) (Y : Ω → γ) (c : γ) : Finset (Fin d → Ω) :=
  Fintype.piFinset fun _ => (univ : Finset Ω).filter fun ω => Y ω = c

omit [DecidableEq Ω] [Fintype γ] in
lemma mem_fibreTuples {d : ℕ} {Y : Ω → γ} {c : γ} {f : Fin d → Ω} :
    f ∈ fibreTuples d Y c ↔ ∀ i, Y (f i) = c := by
  rw [fibreTuples, Fintype.mem_piFinset]
  constructor
  · intro h i
    exact (mem_filter.mp (h i)).2
  · intro h i
    exact mem_filter.mpr ⟨mem_univ _, h i⟩

omit [DecidableEq Ω] [Fintype γ] in
/-- **The weight of a fibre's tuples is `P(Y = c)^d`.** The product-of-sums expansion. -/
lemma sum_fibreTuples (d : ℕ) (w : Ω → ℝ) (Y : Ω → γ) (c : γ) :
    ∑ f ∈ fibreTuples d Y c, ∏ i, w (f i) = (wdist w Y c) ^ d := by
  classical
  rw [fibreTuples, ← Finset.prod_univ_sum (fun _ : Fin d => (univ : Finset Ω).filter
    fun ω => Y ω = c) (fun _ ω => w ω)]
  rw [Finset.prod_const, card_univ, Fintype.card_fin, wdist, wprob]

/-- **`d + 1` conditionally independent copies**, as a weight on `Fin (d+1) → Ω`.

Parametrised by `d + 1` so that the exponent `d` needs no truncated subtraction and the
coordinate `0` exists — `d + 1 ≥ 1` copies is the only case that means anything. -/
noncomputable def condProd (d : ℕ) (w : Ω → ℝ) (Y : Ω → γ) (f : Fin (d + 1) → Ω) : ℝ := by
  classical
  exact if ∀ i, Y (f i) = Y (f 0) then
    (∏ i, w (f i)) / (wdist w Y (Y (f 0))) ^ d else 0

omit [DecidableEq Ω] [Fintype γ] in
lemma condProd_of_const {d : ℕ} {w : Ω → ℝ} {Y : Ω → γ} {f : Fin (d + 1) → Ω}
    (h : ∀ i, Y (f i) = Y (f 0)) :
    condProd d w Y f = (∏ i, w (f i)) / (wdist w Y (Y (f 0))) ^ d := by
  classical
  rw [condProd, if_pos h]

omit [DecidableEq Ω] [Fintype γ] in
lemma condProd_of_not_const {d : ℕ} {w : Ω → ℝ} {Y : Ω → γ} {f : Fin (d + 1) → Ω}
    (h : ¬ ∀ i, Y (f i) = Y (f 0)) : condProd d w Y f = 0 := by
  classical
  rw [condProd, if_neg h]

lemma condProd_nonneg {d : ℕ} {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (Y : Ω → γ)
    (f : Fin (d + 1) → Ω) : 0 ≤ condProd d w Y f := by
  classical
  by_cases h : ∀ i, Y (f i) = Y (f 0)
  · rw [condProd_of_const h]
    have hnum : 0 ≤ ∏ i, w (f i) := Finset.prod_nonneg fun i _ => hw (f i)
    have hden : 0 ≤ (wdist w Y (Y (f 0))) ^ d := by
      refine pow_nonneg ?_ d
      exact wdist_nonneg hw Y _
    positivity
  · rw [condProd_of_not_const h]

/-- **The construction is a probability distribution.** Over a fixed value `c` of `Y` the
tuples weigh `P(c)^{d+1}`, so dividing by `P(c)^d` leaves `P(c)`, and those sum to `1`.

The zero-probability fibres need no separate treatment: there `0 / 0 = 0 = P(c)`. -/
theorem sum_condProd (d : ℕ) {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω = 1)
    (Y : Ω → γ) : ∑ f : Fin (d + 1) → Ω, condProd d w Y f = 1 := by
  classical
  have hmaps : ∀ f ∈ (univ : Finset (Fin (d + 1) → Ω)), Y (f 0) ∈ (univ : Finset γ) :=
    fun f _ => mem_univ _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (condProd d w Y)]
  have hfibre : ∀ c : γ,
      ∑ f ∈ (univ : Finset (Fin (d + 1) → Ω)).filter (fun f => Y (f 0) = c),
        condProd d w Y f = wdist w Y c := by
    intro c
    have hsplit : ∀ f ∈ (univ : Finset (Fin (d + 1) → Ω)).filter (fun f => Y (f 0) = c),
        condProd d w Y f
          = if f ∈ fibreTuples (d + 1) Y c then (∏ i, w (f i)) / (wdist w Y c) ^ d else 0 := by
      intro f hf
      rw [mem_filter] at hf
      by_cases hconst : ∀ i, Y (f i) = Y (f 0)
      · have hmem : f ∈ fibreTuples (d + 1) Y c :=
          mem_fibreTuples.mpr fun i => (hconst i).trans hf.2
        rw [condProd_of_const hconst, if_pos hmem, hf.2]
      · have hnot : f ∉ fibreTuples (d + 1) Y c := by
          intro hmem
          exact hconst fun i => (mem_fibreTuples.mp hmem i).trans
            (mem_fibreTuples.mp hmem 0).symm
        rw [condProd_of_not_const hconst, if_neg hnot]
    rw [Finset.sum_congr rfl hsplit, Finset.sum_ite_mem]
    have hinter : (univ : Finset (Fin (d + 1) → Ω)).filter (fun f => Y (f 0) = c)
        ∩ fibreTuples (d + 1) Y c = fibreTuples (d + 1) Y c := by
      refine Finset.inter_eq_right.mpr fun f hf => ?_
      rw [mem_filter]
      exact ⟨mem_univ _, mem_fibreTuples.mp hf 0⟩
    rw [hinter, ← Finset.sum_div, sum_fibreTuples]
    rcases eq_or_lt_of_le (wdist_nonneg hw Y c) with h | h
    · rw [← h]
      simp
    · rw [pow_succ, mul_comm, mul_div_assoc, div_self (by positivity), mul_one]
  rw [Finset.sum_congr rfl fun c _ => hfibre c, sum_wdist, hsum]

/-- **Each coordinate carries the original law.** Stated against a test function `h`, which
is the form the entropy computations use: coordinate `0` of the `d + 1` copies is
distributed as `w` itself.

Zero-probability fibres are again harmless: if `P(Y = Y ω) = 0` then `w ω = 0` as well,
since `ω` lies in that fibre and the weights are nonnegative. -/
theorem condProd_marginal_zero (d : ℕ) {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (Y : Ω → γ)
    (h : Ω → ℝ) :
    ∑ f : Fin (d + 1) → Ω, condProd d w Y f * h (f 0) = ∑ ω, w ω * h ω := by
  classical
  have key : ∑ f : Fin (d + 1) → Ω, condProd d w Y f * h (f 0)
      = ∑ p : Ω × (Fin d → Ω),
          condProd d w Y (Fin.cons p.1 p.2 : Fin (d + 1) → Ω) * h p.1 :=
    (Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (d + 1) => Ω) _ _ fun _ => rfl).symm
  rw [key, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have hstep : ∀ g : Fin d → Ω,
      condProd d w Y (Fin.cons ω g : Fin (d + 1) → Ω) * h ω
        = (if g ∈ fibreTuples d Y (Y ω) then w ω * (∏ i, w (g i)) / (wdist w Y (Y ω)) ^ d
            else 0) * h ω := by
    intro g
    by_cases hg : g ∈ fibreTuples d Y (Y ω)
    · have hconst : ∀ i : Fin (d + 1), Y ((Fin.cons ω g : Fin (d + 1) → Ω) i) = Y ((Fin.cons ω g : Fin (d + 1) → Ω) 0) := by
        intro i
        rw [Fin.cons_zero]
        refine Fin.cases ?_ ?_ i
        · rw [Fin.cons_zero]
        · intro j
          rw [Fin.cons_succ]
          exact mem_fibreTuples.mp hg j
      rw [condProd_of_const hconst, if_pos hg, Fin.cons_zero, Fin.prod_univ_succ,
        Fin.cons_zero]
      congr 3
    · have hnot : ¬ ∀ i : Fin (d + 1),
          Y ((Fin.cons ω g : Fin (d + 1) → Ω) i)
            = Y ((Fin.cons ω g : Fin (d + 1) → Ω) 0) := by
        intro hconst
        refine hg (mem_fibreTuples.mpr fun j => ?_)
        have hj := hconst j.succ
        rw [Fin.cons_succ, Fin.cons_zero] at hj
        exact hj
      rw [condProd_of_not_const hnot, if_neg hg]
  rw [Finset.sum_congr rfl fun g (_ : g ∈ (univ : Finset (Fin d → Ω))) => hstep g,
    ← Finset.sum_mul, Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_div,
    ← Finset.mul_sum, sum_fibreTuples]
  rcases eq_or_lt_of_le (wdist_nonneg hw Y (Y ω)) with hz | hpos
  · have hwz : w ω = 0 := by
      have hmem : ω ∈ (univ : Finset Ω).filter fun x => Y x = Y ω :=
        mem_filter.mpr ⟨mem_univ _, rfl⟩
      have hle : w ω ≤ wdist w Y (Y ω) :=
        Finset.single_le_sum (f := w) (fun x _ => hw x) hmem
      exact le_antisymm (by rw [← hz] at hle; exact hle) (hw ω)
    rw [hwz]
    simp
  · rw [mul_div_assoc, div_self (by positivity), mul_one]

end CondCopies

end PMC
