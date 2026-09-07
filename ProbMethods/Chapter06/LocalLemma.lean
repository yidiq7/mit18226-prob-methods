import ProbMethods.Weighted

/-!
# §6.1 — The Lovász Local Lemma

Zhao, *Probabilistic Methods in Combinatorics*, Theorem 6.1.x.

Mathlib has no local lemma, and unlike Talagrand or the container theorem this one is
fully expressible in the finite weighted framework of `ProbMethods/Weighted.lean`: events
are `Finset`s of a finite sample space, `PMC.wprob` is their probability, and the
dependency structure is a neighbour map `N : ι → Finset ι`.

Intersections of complements are written `T.inf (fun j => (A j)ᶜ)`, which is `⋂ j ∈ T, (A j)ᶜ`
and is `univ` when `T = ∅` — exactly the convention the induction needs.
-/

open Finset

namespace PMC

section LocalLemma

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- The event that none of the `A j` for `j ∈ T` occurs. -/
def noneOf (A : ι → Finset Ω) (T : Finset ι) : Finset Ω := T.inf fun j => (A j)ᶜ

@[simp] lemma noneOf_empty (A : ι → Finset Ω) : noneOf A ∅ = (univ : Finset Ω) := by
  simp [noneOf]

lemma noneOf_insert (A : ι → Finset Ω) (i : ι) (T : Finset ι) :
    noneOf A (insert i T) = (A i)ᶜ ∩ noneOf A T := by
  simp [noneOf, Finset.inf_insert]

lemma noneOf_subset (A : ι → Finset Ω) {T U : Finset ι} (h : T ⊆ U) :
    noneOf A U ⊆ noneOf A T := Finset.inf_mono h

/-- The peeling step: given the main bound for all *strictly smaller* index sets, the
probability that none of `U ∪ V` occurs is at least `∏ j ∈ U, (1 - x j)` times the
probability that none of `V` occurs.

Kept multiplicative — no division by a probability not yet known to be positive. -/
private lemma lll_peel (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (A : ι → Finset Ω) (x : ι → ℝ) (hx1 : ∀ i, x i < 1) (n : ℕ)
    (IH : ∀ m, m < n → ∀ T : Finset ι, #T = m → ∀ i, i ∉ T →
      wprob w (A i ∩ noneOf A T) ≤ x i * wprob w (noneOf A T)) :
    ∀ U V : Finset ι, Disjoint U V → #U + #V ≤ n →
      (∏ j ∈ U, (1 - x j)) * wprob w (noneOf A V) ≤ wprob w (noneOf A (U ∪ V)) := by
  intro U
  induction U using Finset.induction_on with
  | empty =>
    intro V _ _
    simp
  | insert j₀ U' hj₀ ih =>
    intro V hdisj hcard
    have hjV : j₀ ∉ V := by
      intro hj
      exact (Finset.disjoint_left.mp hdisj (mem_insert_self j₀ U')) hj
    have hdisj' : Disjoint U' V :=
      Finset.disjoint_of_subset_left (subset_insert _ _) hdisj
    have hcardU : #(insert j₀ U') = #U' + 1 := card_insert_of_notMem hj₀
    have hjUV : j₀ ∉ U' ∪ V := by
      rw [mem_union]
      exact fun h => h.elim hj₀ hjV
    have hcardUV : #(U' ∪ V) = #U' + #V := card_union_of_disjoint hdisj'
    have hlt : #(U' ∪ V) < n := by omega
    have hmain := IH (#(U' ∪ V)) hlt (U' ∪ V) rfl j₀ hjUV
    have hih := ih V hdisj' (by omega)
    have hsets : insert j₀ U' ∪ V = insert j₀ (U' ∪ V) := by
      rw [Finset.insert_union]
    have hsplit : wprob w (noneOf A (insert j₀ (U' ∪ V)))
        = wprob w (noneOf A (U' ∪ V)) - wprob w (A j₀ ∩ noneOf A (U' ∪ V)) := by
      rw [noneOf_insert, wprob_compl_inter]
    have hx0j : (0 : ℝ) ≤ 1 - x j₀ := by linarith [hx1 j₀]
    rw [hsets, hsplit, prod_insert hj₀, mul_assoc]
    calc (1 - x j₀) * ((∏ j ∈ U', (1 - x j)) * wprob w (noneOf A V))
        ≤ (1 - x j₀) * wprob w (noneOf A (U' ∪ V)) :=
          mul_le_mul_of_nonneg_left hih hx0j
      _ = wprob w (noneOf A (U' ∪ V)) - x j₀ * wprob w (noneOf A (U' ∪ V)) := by ring
      _ ≤ wprob w (noneOf A (U' ∪ V)) - wprob w (A j₀ ∩ noneOf A (U' ∪ V)) := by
          linarith [hmain]

/-- The main inductive bound: conditioned on none of `T` occurring, `A i` still has
probability at most `x i`. Stated multiplicatively. -/
private lemma lll_key (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (A : ι → Finset Ω) (N : ι → Finset ι) (x : ι → ℝ)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hself : ∀ i, i ∉ N i)
    (hindep : ∀ (i : ι) (T : Finset ι), Disjoint T (insert i (N i)) →
      wprob w (A i ∩ noneOf A T) = wprob w (A i) * wprob w (noneOf A T))
    (hbound : ∀ i, wprob w (A i) ≤ x i * ∏ j ∈ N i, (1 - x j)) :
    ∀ (n : ℕ) (T : Finset ι), #T = n → ∀ i, i ∉ T →
      wprob w (A i ∩ noneOf A T) ≤ x i * wprob w (noneOf A T) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro T hT i hi
    classical
    have hT1sub : T ∩ N i ⊆ N i := inter_subset_right
    have hT2sub : T \ N i ⊆ T := sdiff_subset
    have hdisj12 : Disjoint (T ∩ N i) (T \ N i) := by
      rw [Finset.disjoint_left]
      intro a ha ha'
      exact (mem_sdiff.mp ha').2 (mem_inter.mp ha).2
    have hsplit : (T ∩ N i) ∪ (T \ N i) = T := by
      ext a
      simp only [mem_union, mem_inter, mem_sdiff]
      constructor
      · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
      · intro h
        by_cases hN : a ∈ N i
        · exact Or.inl ⟨h, hN⟩
        · exact Or.inr ⟨h, hN⟩
    -- independence across the part of `T` outside `N i`
    have hdisjT2 : Disjoint (T \ N i) (insert i (N i)) := by
      rw [Finset.disjoint_left]
      intro a ha ha'
      rw [mem_insert] at ha'
      rcases ha' with rfl | ha'
      · exact hi (mem_sdiff.mp ha).1
      · exact (mem_sdiff.mp ha).2 ha'
    have hind := hindep i (T \ N i) hdisjT2
    -- the numerator only gets smaller when we drop the constraints in `T ∩ N i`
    have hmono : wprob w (A i ∩ noneOf A T) ≤ wprob w (A i ∩ noneOf A (T \ N i)) := by
      refine wprob_mono hw (Finset.inter_subset_inter Subset.rfl ?_)
      exact noneOf_subset A hT2sub
    -- the denominator, by peeling `T ∩ N i`
    have hpeel := lll_peel w hw A x hx1 n IH (T ∩ N i) (T \ N i) hdisj12
      (by rw [← card_union_of_disjoint hdisj12, hsplit, hT])
    rw [hsplit] at hpeel
    -- products: more factors means a smaller product
    have hprod : (∏ j ∈ N i, (1 - x j)) ≤ ∏ j ∈ T ∩ N i, (1 - x j) := by
      refine Finset.prod_le_prod_of_subset_of_le_one hT1sub (fun j _ => ?_) (fun j _ _ => ?_)
      · linarith [hx1 j]
      · linarith [hx0 j]
    have hp2nonneg : 0 ≤ wprob w (noneOf A (T \ N i)) := wprob_nonneg hw _
    have hprodnonneg : (0 : ℝ) ≤ ∏ j ∈ T ∩ N i, (1 - x j) :=
      Finset.prod_nonneg fun j _ => by linarith [hx1 j]
    calc wprob w (A i ∩ noneOf A T)
        ≤ wprob w (A i ∩ noneOf A (T \ N i)) := hmono
      _ = wprob w (A i) * wprob w (noneOf A (T \ N i)) := hind
      _ ≤ (x i * ∏ j ∈ N i, (1 - x j)) * wprob w (noneOf A (T \ N i)) :=
          mul_le_mul_of_nonneg_right (hbound i) hp2nonneg
      _ ≤ (x i * ∏ j ∈ T ∩ N i, (1 - x j)) * wprob w (noneOf A (T \ N i)) := by
          refine mul_le_mul_of_nonneg_right ?_ hp2nonneg
          exact mul_le_mul_of_nonneg_left hprod (hx0 i)
      _ = x i * ((∏ j ∈ T ∩ N i, (1 - x j)) * wprob w (noneOf A (T \ N i))) := by ring
      _ ≤ x i * wprob w (noneOf A T) := mul_le_mul_of_nonneg_left hpeel (hx0 i)

/-- **The Lovász Local Lemma**, asymmetric form (Zhao, Theorem 6.1.x).

If each event `A i` has probability at most `x i * ∏ j ∈ N i, (1 - x j)`, and each `A i` is
independent of any family of complements drawn from outside `insert i (N i)`, then with
positive probability none of the events occurs — indeed the probability is at least
`∏ i, (1 - x i)`, which is positive because each `x i < 1`.

The independence hypothesis is the standard one, stated here as an equality of weights for
every subfamily `T` disjoint from `insert i (N i)`. That "for every subfamily" is essential
and is what mutual independence means; pairwise independence is not enough.

**Proof strategy** (the part a prover has to supply). By induction on `#T`, show

    ∀ i ∉ T,  wprob w (A i ∩ noneOf A T) ≤ x i * wprob w (noneOf A T)

Split `T` as `T₁ = T ∩ N i` and `T₂ = T \ N i`. The numerator is bounded using
independence across `T₂`, giving `wprob w (A i) * wprob w (noneOf A T₂)`; the denominator is
bounded below by `∏ j ∈ T₁, (1 - x j)` times `wprob w (noneOf A T₂)` using the inductive
hypothesis on the strictly smaller sets obtained by peeling `T₁` one element at a time.
Since `T₁ ⊆ N i`, the product `∏ j ∈ N i, (1 - x j)` in `hbound` dominates
`∏ j ∈ T₁, (1 - x j)` and the ratio collapses to `x i`.

The conclusion then follows by a second induction, on `S`, from
`wprob w (noneOf A (insert i S)) ≥ (1 - x i) * wprob w (noneOf A S)`.

Both inductions are genuinely needed, and the conditional-probability bookkeeping of the
informal proof has to be replaced by multiplicative inequalities to avoid dividing by a
quantity not yet known to be positive. -/
theorem lovasz_local_lemma (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω = 1)
    (A : ι → Finset Ω) (N : ι → Finset ι) (x : ι → ℝ)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hself : ∀ i, i ∉ N i)
    (hindep : ∀ (i : ι) (T : Finset ι), Disjoint T (insert i (N i)) →
      wprob w (A i ∩ noneOf A T) = wprob w (A i) * wprob w (noneOf A T))
    (hbound : ∀ i, wprob w (A i) ≤ x i * ∏ j ∈ N i, (1 - x j)) :
    ∏ i, (1 - x i) ≤ wprob w (noneOf A (univ : Finset ι)) := by
  have hIH : ∀ m, m < Fintype.card ι + 1 → ∀ T : Finset ι, #T = m → ∀ i, i ∉ T →
      wprob w (A i ∩ noneOf A T) ≤ x i * wprob w (noneOf A T) :=
    fun m _ => lll_key w hw A N x hx0 hx1 hself hindep hbound m
  have h := lll_peel w hw A x hx1 (Fintype.card ι + 1) hIH
    (univ : Finset ι) (∅ : Finset ι) (by simp) (by simp)
  rw [Finset.union_empty, noneOf_empty, wprob_univ, hsum, mul_one] at h
  exact h

end LocalLemma

end PMC
