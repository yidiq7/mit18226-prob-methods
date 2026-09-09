import ProbMethods.Chapter10.Shearer

/-!
# §10.3 — Counting by entropy: the Loomis–Whitney inequality

Zhao, *Probabilistic Methods in Combinatorics*, Chapter 10.

Shearer's lemma turns into a counting statement the moment the random variable is uniform
on the set being counted. The two halves of the conversion are

* `PMC.wentropy_uniform_of_injective` — the whole tuple determines the point, so its entropy
  is exactly `log #A`;
* `PMC.wentropy_le_log_card_image` — a masked tuple takes at most `#(trace of A on S)`
  values, so its entropy is at most the log of that.

Feeding both into `PMC.shearer` gives `PMC.card_pow_le_prod_card_projSet`: if every
coordinate is covered `k` times by the family, then `#A ^ k ≤ ∏ #(trace on A j)`. Loomis–
Whitney is the case of the three 2-element subsets of a 3-coordinate tuple, giving
`#A ^ 2 ≤ #A_yz · #A_xz · #A_xy`.
-/

open Finset

namespace PMC

section Counting

variable {ι : Type*} [Fintype ι] [LinearOrder ι] {β : Type*} [Fintype β] [DecidableEq β]

/-- The **trace** of `A` on the coordinates in `S`: the distinct patterns the members of
`A` show on `S`. Recorded as masked tuples so that all traces live in one type. -/
def projSet (S : Finset ι) (A : Finset (ι → β)) : Finset (ι → Option β) :=
  A.image fun x i => if i ∈ S then some (x i) else none

lemma mem_projSet {S : Finset ι} {A : Finset (ι → β)} {u : ι → Option β} :
    u ∈ projSet S A ↔ ∃ x ∈ A, (fun i => if i ∈ S then some (x i) else none) = u := by
  rw [projSet, Finset.mem_image]

lemma projSet_nonempty {A : Finset (ι → β)} (hA : A.Nonempty) (S : Finset ι) :
    (projSet S A).Nonempty := hA.image _

/-- **Shearer's lemma as a counting statement.**

If every coordinate lies in at least `k` of the sets `S j`, `j ∈ F`, then
`#A ^ k ≤ ∏_{j ∈ F} #(trace of A on S j)`. -/
theorem card_pow_le_prod_card_projSet (A : Finset (ι → β)) (hA : A.Nonempty)
    {κ : Type*} [DecidableEq κ] (F : Finset κ) (S : κ → Finset ι) (k : ℕ)
    (hcov : ∀ i : ι, k ≤ #(F.filter fun j => i ∈ S j)) :
    (#A : ℝ) ^ k ≤ ∏ j ∈ F, (#(projSet (S j) A) : ℝ) := by
  classical
  -- the uniform distribution on `A`
  set Ω := {x : ι → β // x ∈ A} with hΩdef
  have hcard : Fintype.card Ω = #A := Fintype.card_coe A
  have hApos : 0 < #A := Finset.card_pos.mpr hA
  have hNpos : 0 < Fintype.card Ω := by rw [hcard]; exact hApos
  have hNR : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast hNpos
  set w : Ω → ℝ := fun _ => 1 / Fintype.card Ω with hwdef
  have hw : ∀ ω, 0 ≤ w ω := fun ω => by rw [hwdef]; positivity
  have hsum : ∑ ω, w ω = 1 := by
    rw [hwdef, Finset.sum_const, card_univ, nsmul_eq_mul, mul_one_div, div_self (ne_of_gt hNR)]
  set X : ι → Ω → β := fun i ω => (ω : ι → β) i with hXdef
  -- the whole tuple determines the point
  have hinj : Function.Injective (masked X (univ : Finset ι)) := by
    intro ω ω' h
    apply Subtype.ext
    funext i
    have hi := congrFun h i
    simp only [masked, mem_univ, if_true, hXdef] at hi
    exact Option.some_injective _ hi
  have huniv : tupleEntropy w X (univ : Finset ι) = Real.log #A := by
    rw [tupleEntropy, hwdef, wentropy_uniform_of_injective hinj hNpos, hcard]
  -- a masked tuple takes exactly the values in the trace
  have himg : ∀ T : Finset ι,
      (univ : Finset Ω).image (masked X T) = projSet T A := by
    intro T
    ext u
    simp only [Finset.mem_image, mem_univ, true_and, projSet, masked, hXdef]
    exact ⟨fun ⟨ω, hω⟩ => ⟨ω.1, ω.2, hω⟩, fun ⟨x, hx, hxu⟩ => ⟨⟨x, hx⟩, hxu⟩⟩
  have hle : ∀ j : κ, tupleEntropy w X (S j) ≤ Real.log #(projSet (S j) A) := by
    intro j
    rw [tupleEntropy, ← himg (S j)]
    exact wentropy_le_log_card_image hw hsum (masked X (S j))
  -- Shearer, then convert logs back to counts
  have hsh := shearer hw hsum X F S k hcov
  rw [huniv] at hsh
  have hstep : (k : ℝ) * Real.log #A ≤ ∑ j ∈ F, Real.log #(projSet (S j) A) :=
    hsh.trans (Finset.sum_le_sum fun j _ => hle j)
  have hpospr : ∀ j ∈ F, ((#(projSet (S j) A) : ℝ)) ≠ 0 := by
    intro j _
    have := Finset.card_pos.mpr (projSet_nonempty hA (S j))
    positivity
  have hlogprod : Real.log (∏ j ∈ F, (#(projSet (S j) A) : ℝ))
      = ∑ j ∈ F, Real.log #(projSet (S j) A) := Real.log_prod hpospr
  have hlogpow : Real.log ((#A : ℝ) ^ k) = (k : ℝ) * Real.log #A := Real.log_pow _ k
  have hApos' : (0 : ℝ) < (#A : ℝ) ^ k := by
    have : (0 : ℝ) < #A := by exact_mod_cast hApos
    positivity
  have hprodpos : (0 : ℝ) < ∏ j ∈ F, (#(projSet (S j) A) : ℝ) :=
    Finset.prod_pos fun j _ => by
      have := Finset.card_pos.mpr (projSet_nonempty hA (S j))
      exact_mod_cast this
  calc ((#A : ℝ)) ^ k = Real.exp (Real.log ((#A : ℝ) ^ k)) := (Real.exp_log hApos').symm
    _ ≤ Real.exp (Real.log (∏ j ∈ F, (#(projSet (S j) A) : ℝ))) :=
        Real.exp_le_exp.mpr (by rw [hlogpow, hlogprod]; exact hstep)
    _ = ∏ j ∈ F, (#(projSet (S j) A) : ℝ) := Real.exp_log hprodpos

/-- **The Loomis–Whitney inequality** (Zhao, Chapter 10).

A finite set of points in three coordinates is bounded by the product of the sizes of its
three axis-plane shadows: `#A ^ 2 ≤ #A_{yz} · #A_{xz} · #A_{xy}`.

The three 2-element subsets of `Fin 3` cover each coordinate exactly twice, so this is
`PMC.card_pow_le_prod_card_projSet` at `k = 2`. -/
theorem loomis_whitney (A : Finset (Fin 3 → β)) (hA : A.Nonempty) :
    (#A : ℝ) ^ 2 ≤ ∏ j : Fin 3, (#(projSet (univ \ {j}) A) : ℝ) := by
  refine card_pow_le_prod_card_projSet A hA univ (fun j => univ \ {j}) 2 ?_
  intro i
  have hf : (univ : Finset (Fin 3)).filter
      (fun j => i ∈ (univ : Finset (Fin 3)) \ {j}) = univ.erase i := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_sdiff, mem_singleton, mem_erase, and_true]
    exact ne_comm
  rw [hf, Finset.card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]

end Counting

end PMC
