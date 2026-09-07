import ProbMethods.Chapter10.Entropy

/-!
# §10.2 — Shearer's lemma

Zhao, *Probabilistic Methods in Combinatorics*, Chapter 10.

Shearer's lemma says that if every coordinate is covered at least `k` times by a family of
index sets, then `k · H(X) ≤ ∑ H(X_S)` over the family.

The proof here is split in two. `ProbMethods/Chapter10/Entropy.lean` established that
`S ↦ H(X_S)` is normalised at `∅`, monotone, and submodular in diminishing-returns form.
**Everything below that point is a statement about set functions with no entropy in it**,
proved here as `PMC.shearer_of_submodular`, with `PMC.shearer` the entropy instance. The
split is worth it: the combinatorial half is where the content is, and it is reusable for
any other submodular quantity.

The mechanism is the *chain decomposition* `PMC.sum_chain_eq`: fixing a linear order on the
coordinates, `f S = ∑ i ∈ S, (f (insert i (S ∩ prefixLt i)) - f (S ∩ prefixLt i))`, which
telescopes when you peel off the largest element of `S`. Submodularity then replaces each
increment by the one taken over the *whole* prefix, which no longer depends on `S`; summing
over the family and counting each coordinate's multiplicity finishes it.
-/

open Finset

namespace PMC

section Submodular

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The set of coordinates strictly below `i`. -/
def prefixLt (i : ι) : Finset ι := univ.filter fun x => x < i

@[simp] lemma mem_prefixLt {i x : ι} : x ∈ prefixLt i ↔ x < i := by simp [prefixLt]

variable (f : Finset ι → ℝ)

/-- The gain from adding `i` to everything below it. Independent of any ambient set — that
independence is what makes the double count at the end work. -/
def gain (i : ι) : ℝ := f (insert i (prefixLt i)) - f (prefixLt i)

/-- **The chain decomposition.** Peeling off the largest element of `S` telescopes. -/
theorem sum_chain_eq (hempty : f ∅ = 0) (S : Finset ι) :
    ∑ i ∈ S, (f (insert i (S ∩ prefixLt i)) - f (S ∩ prefixLt i)) = f S := by
  classical
  induction S using Finset.strongInduction with
  | _ S ih =>
    rcases S.eq_empty_or_nonempty with rfl | hS
    · simp [hempty]
    · obtain ⟨m, hm, hmax⟩ := S.exists_max_image id hS
      have hpre : S ∩ prefixLt m = S.erase m := by
        ext x
        simp only [mem_inter, mem_prefixLt, mem_erase]
        exact ⟨fun h => ⟨ne_of_lt h.2, h.1⟩,
          fun h => ⟨h.2, lt_of_le_of_ne (hmax x h.2) h.1⟩⟩
      have hterms : ∀ i ∈ S.erase m, S ∩ prefixLt i = S.erase m ∩ prefixLt i := by
        intro i hi
        rw [mem_erase] at hi
        ext x
        simp only [mem_inter, mem_prefixLt, mem_erase]
        refine ⟨fun h => ⟨⟨?_, h.1⟩, h.2⟩, fun h => ⟨h.1.2, h.2⟩⟩
        intro hxm
        exact absurd (hxm ▸ h.2) (not_lt_of_ge (hmax i hi.2))
      rw [← Finset.add_sum_erase _ _ hm, hpre, Finset.insert_erase hm,
        Finset.sum_congr rfl fun i hi => by rw [hterms i hi], ih (S.erase m)
        (Finset.erase_ssubset hm)]
      ring

theorem gain_nonneg (hmono : ∀ {S T : Finset ι}, S ⊆ T → f S ≤ f T) (i : ι) :
    0 ≤ gain f i := sub_nonneg.mpr (hmono (Finset.subset_insert i _))

/-- The chain decomposition at `S = univ`, where the increments are exactly the gains. -/
theorem sum_gain_eq (hempty : f ∅ = 0) : ∑ i : ι, gain f i = f univ := by
  calc ∑ i : ι, gain f i
      = ∑ i ∈ (univ : Finset ι),
          (f (insert i (univ ∩ prefixLt i)) - f (univ ∩ prefixLt i)) :=
        Finset.sum_congr rfl fun i _ => by rw [Finset.univ_inter, gain]
    _ = f univ := sum_chain_eq f hempty univ

/-- Submodularity turns the chain decomposition into a **lower bound valid for every `S`**,
with increments that no longer depend on `S`. -/
theorem sum_gain_le (hempty : f ∅ = 0)
    (hsub : ∀ {T T' : Finset ι}, T ⊆ T' → ∀ i,
      f (insert i T') - f T' ≤ f (insert i T) - f T) (S : Finset ι) :
    ∑ i ∈ S, gain f i ≤ f S := by
  calc ∑ i ∈ S, gain f i
      ≤ ∑ i ∈ S, (f (insert i (S ∩ prefixLt i)) - f (S ∩ prefixLt i)) :=
        Finset.sum_le_sum fun i _ => hsub Finset.inter_subset_right i
    _ = f S := sum_chain_eq f hempty S

/-- **Shearer's lemma for submodular set functions.**

If `f` is normalised, monotone and submodular, and every coordinate lies in at least `k`
of the sets `A j` for `j ∈ F`, then `k · f univ ≤ ∑_{j ∈ F} f (A j)`.

`F` is indexed rather than being a family of sets directly, so repeated sets are allowed —
which is the generality Shearer's applications use. -/
theorem shearer_of_submodular (hempty : f ∅ = 0)
    (hmono : ∀ {S T : Finset ι}, S ⊆ T → f S ≤ f T)
    (hsub : ∀ {T T' : Finset ι}, T ⊆ T' → ∀ i,
      f (insert i T') - f T' ≤ f (insert i T) - f T)
    {κ : Type*} [DecidableEq κ] (F : Finset κ) (A : κ → Finset ι) (k : ℕ)
    (hcov : ∀ i : ι, k ≤ #(F.filter fun j => i ∈ A j)) :
    (k : ℝ) * f univ ≤ ∑ j ∈ F, f (A j) := by
  classical
  have hswap : ∑ j ∈ F, ∑ i ∈ A j, gain f i
      = ∑ i : ι, (#(F.filter fun j => i ∈ A j) : ℝ) * gain f i := by
    calc ∑ j ∈ F, ∑ i ∈ A j, gain f i
        = ∑ j ∈ F, ∑ i : ι, (if i ∈ A j then gain f i else 0) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← Finset.sum_filter]
          exact Finset.sum_congr (by ext i; simp) fun _ _ => rfl
      _ = ∑ i : ι, ∑ j ∈ F, (if i ∈ A j then gain f i else 0) := Finset.sum_comm
      _ = ∑ i : ι, (#(F.filter fun j => i ∈ A j) : ℝ) * gain f i :=
          Finset.sum_congr rfl fun i _ => by
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  calc (k : ℝ) * f univ = (k : ℝ) * ∑ i : ι, gain f i := by rw [sum_gain_eq f hempty]
    _ = ∑ i : ι, (k : ℝ) * gain f i := Finset.mul_sum ..
    _ ≤ ∑ i : ι, (#(F.filter fun j => i ∈ A j) : ℝ) * gain f i :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcov i) (gain_nonneg f hmono i)
    _ = ∑ j ∈ F, ∑ i ∈ A j, gain f i := hswap.symm
    _ ≤ ∑ j ∈ F, f (A j) := Finset.sum_le_sum fun j _ => sum_gain_le f hempty hsub (A j)

end Submodular

/-- **Shearer's lemma** (Zhao, Chapter 10).

If every coordinate of the tuple `X` lies in at least `k` of the index sets `A j`, `j ∈ F`,
then `k · H(X) ≤ ∑_{j ∈ F} H(X_{A j})`.

This is `PMC.shearer_of_submodular` instantiated at `S ↦ H(X_S)`, whose three hypotheses
are `PMC.tupleEntropy_empty`, `PMC.tupleEntropy_mono` and `PMC.tupleEntropy_submodular`. -/
theorem shearer {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {β : Type*} [Fintype β]
    [DecidableEq β] {ι : Type*} [Fintype ι] [LinearOrder ι] {w : Ω → ℝ}
    (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω = 1) (X : ι → Ω → β)
    {κ : Type*} [DecidableEq κ] (F : Finset κ) (A : κ → Finset ι) (k : ℕ)
    (hcov : ∀ i : ι, k ≤ #(F.filter fun j => i ∈ A j)) :
    (k : ℝ) * tupleEntropy w X univ ≤ ∑ j ∈ F, tupleEntropy w X (A j) :=
  shearer_of_submodular (tupleEntropy w X) (tupleEntropy_empty hsum X)
    (fun h => tupleEntropy_mono hw X h)
    (fun h i => tupleEntropy_submodular hw hsum X h i) F A k hcov

end PMC
