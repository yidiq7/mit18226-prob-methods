import ProbMethods.Chapter07.Correlation

/-!
# §8.1 — Janson's inequality: the lower bound

Zhao, *Probabilistic Methods in Combinatorics*, Theorem 8.1.1.

The setting is a random subset `S` of a finite ground set `α`, each element `x` included
independently with probability `p x` — that is, the weight `PMC.pweight p`. Given a family
of "bad" sets `g : ι → Finset α`, the event `A i` is "`g i ⊆ S`", and Janson's inequality
sandwiches the probability that no `A i` occurs:

`∏ i, (1 - P (A i))  ≤  P (no A i occurs)  ≤  exp (-μ + Δ/2)`.

This file proves the **lower bound**, which is Harris' inequality: the events `¬ A i` are
all *decreasing*, so they are positively correlated
(`PMC.pweight_correlate_anti_family`). Mathlib has no Janson inequality; it does have the
four functions theorem, which is what `PMC.pweight_fkg_anti` rests on.

The upper bound is a genuinely different argument (conditioning on a prefix of the family)
and is not proved here.
-/

open Finset

namespace PMC

section Janson

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The probability that a given set `B` is *not* contained in the random subset. -/
theorem sum_pweight_not_superset (p : α → ℝ) (B : Finset α) :
    ∑ S ∈ (univ : Finset (Finset α)).filter (fun S => ¬ B ⊆ S), pweight p S
      = 1 - ∏ i ∈ B, p i := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not (univ : Finset (Finset α))
    (fun S => B ⊆ S) (pweight p)
  have htot : ∑ S : Finset α, pweight p S = 1 := by
    have h := sum_pweight (α := α) p
    rwa [Finset.powerset_univ] at h
  have hsup : ∑ S ∈ (univ : Finset (Finset α)).filter (fun S => B ⊆ S), pweight p S
      = ∏ i ∈ B, p i := by
    have h := sum_pweight_superset p B
    rwa [Finset.powerset_univ] at h
  rw [htot, hsup] at hsplit
  linarith

/-- **Janson's inequality, lower bound** (Zhao, Theorem 8.1.1).

If each `x : α` is kept independently with probability `p x`, then the probability that
none of the sets `g i` survives in full is at least `∏ i, (1 - ∏ x ∈ g i, p x)` — the value
it would have if the events were independent.

The events "`g i` is not contained in the random set" are decreasing, so Harris' inequality
applies: decreasing events are positively correlated, and correlation only helps. Note that
no hypothesis relates the `g i` to each other — overlapping sets are exactly the
interesting case, and the bound holds regardless. -/
theorem janson_lower (p : α → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → Finset α) :
    ∏ i, (1 - ∏ x ∈ g i, p x)
      ≤ ∑ S ∈ (univ : Finset (Finset α)).filter (fun S => ∀ i, ¬ g i ⊆ S), pweight p S := by
  have h := pweight_correlate_anti_family p hp0 hp1 (fun i S => ¬ g i ⊆ S)
    (fun i S T hST hT hS => hT (hS.trans hST)) (univ : Finset ι)
  have hfac : ∀ i : ι,
      (∑ S ∈ (univ : Finset (Finset α)).filter (fun S => ¬ g i ⊆ S), pweight p S)
        = 1 - ∏ x ∈ g i, p x := fun i => sum_pweight_not_superset p (g i)
  rw [Finset.prod_congr rfl fun i _ => hfac i] at h
  refine h.trans (le_of_eq (Finset.sum_congr ?_ fun _ _ => rfl))
  ext S
  simp

/-- **Janson's lower bound in `G(n, p)`.**

The same statement at a constant probability, which is the form the applications use: over
the ground set `α` — for a random graph, `Sym2 V` — each element kept independently with
probability `p`, the chance that none of the sets `g i` appears in full is at least
`∏ i, (1 - p ^ #(g i))`.

Uses `PMC.bweight_eq_pweight`, the bridge between the two weight families. -/
theorem janson_lower_const (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → Finset α) :
    ∏ i, (1 - p ^ #(g i))
      ≤ ∑ S ∈ (univ : Finset (Finset α)).filter (fun S => ∀ i, ¬ g i ⊆ S), bweight p S := by
  have h := janson_lower (fun _ : α => p) (fun _ => hp0) (fun _ => hp1) g
  rw [Finset.prod_congr rfl fun i _ => by rw [Finset.prod_const]] at h
  refine h.trans (le_of_eq (Finset.sum_congr rfl fun S _ => ?_))
  rw [bweight_eq_pweight]

end Janson

end PMC
