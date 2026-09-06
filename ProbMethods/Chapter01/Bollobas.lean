import ProbMethods.Basic

/-!
# §1.2 — Bollobás' two families theorem

Zhao, *Probabilistic Methods in Combinatorics*, Theorems 1.2.4 and 1.2.6.

Sperner's theorem (1.2.2), the LYM inequality (1.2.3) and the Erdős–Ko–Rado theorem
(1.2.9) are already in Mathlib, as `IsAntichain.sperner`,
`Finset.lubell_yamamoto_meshalkin_inequality_sum_inv_choose` and `Finset.erdos_ko_rado`.
-/

open Finset

namespace PMC

variable {α : Type*} [DecidableEq α]

/-- **Bollobás' two families theorem** (Zhao, Theorem 1.2.6; Bollobás 1965).

If `A i ∩ B i = ∅` for every `i`, and `A i ∩ B j ≠ ∅` whenever `i ≠ j`, then
`∑ i, (#(A i) + #(B i)).choose (#(A i)) ⁻¹ ≤ 1`.

The book's proof takes a uniformly random ordering of `⋃ i, (A i ∪ B i)` and lets `E i` be
the event that every element of `A i` precedes every element of `B i`, an event of
probability `((#(A i) + #(B i)).choose (#(A i)))⁻¹`. The hypotheses force the `E i` to be
pairwise disjoint, so their probabilities sum to at most `1`. -/
theorem sum_inv_choose_le_one {m : ℕ} (A B : Fin m → Finset α)
    (hdisj : ∀ i, Disjoint (A i) (B i))
    (hcross : ∀ i j, i ≠ j → (A i ∩ B j).Nonempty) :
    ∑ i, (1 : ℝ) / ((#(A i) + #(B i)).choose (#(A i))) ≤ 1 := by
  sorry

/-- **Bollobás' two families theorem, uniform case** (Zhao, Theorem 1.2.4).

If the `A i` are `r`-element sets, the `B i` are `s`-element sets, `A i ∩ B i = ∅` for all
`i` and `A i ∩ B j ≠ ∅` for all `i ≠ j`, then `m ≤ (r + s).choose r`.

This is the special case of `PMC.sum_inv_choose_le_one` in which every summand equals
`((r + s).choose r)⁻¹`. -/
theorem card_le_choose_of_two_families {m r s : ℕ} (A B : Fin m → Finset α)
    (hA : ∀ i, #(A i) = r) (hB : ∀ i, #(B i) = s)
    (hdisj : ∀ i, Disjoint (A i) (B i))
    (hcross : ∀ i j, i ≠ j → (A i ∩ B j).Nonempty) :
    m ≤ (r + s).choose r := by
  sorry

end PMC
