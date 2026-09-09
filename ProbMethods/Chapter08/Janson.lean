import ProbMethods.Chapter07.Correlation
import ProbMethods.Chapter06.Coloring

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


/-! ## The upper bound

Kept **multiplicative**, exactly as §6.1 kept the local lemma multiplicative: the informal
proof divides by `P(⋂_{j<i} Ā_j)`, and that division is the only thing that would force a
case analysis on whether the prefix has positive probability. Stating each step as
`P(D ∩ Āᵢ) ≤ c · P(D)` avoids it entirely.
-/

section Upper

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The event that the bad set `g i` survives in full. -/
def badEvent (g : ι → Finset α) (i : ι) : Finset (Finset α) :=
  (univ : Finset (Finset α)).filter fun S => g i ⊆ S

@[simp] lemma mem_badEvent {g : ι → Finset α} {i : ι} {S : Finset α} :
    S ∈ badEvent g i ↔ g i ⊆ S := by simp [badEvent]

lemma badEvent_mono (g : ι → Finset α) (i : ι) {S T : Finset α} (hST : S ⊆ T)
    (hS : S ∈ badEvent g i) : T ∈ badEvent g i := by
  rw [mem_badEvent] at hS ⊢
  exact hS.trans hST

/-- `g i` surviving depends only on the coordinates of `g i` — the fact that makes the
far-away part of the family genuinely independent rather than merely correlated. -/
lemma determinedBy_badEvent (g : ι → Finset α) (i : ι) :
    DeterminedBy (g i) (badEvent g i) := by
  intro S T hST
  simp only [mem_badEvent]
  constructor
  · intro h x hx
    have hxS : x ∈ S ∩ g i := mem_inter.mpr ⟨h hx, hx⟩
    rw [hST] at hxS
    exact (mem_inter.mp hxS).1
  · intro h x hx
    have hxT : x ∈ T ∩ g i := mem_inter.mpr ⟨h hx, hx⟩
    rw [← hST] at hxT
    exact (mem_inter.mp hxT).1

lemma noneOf_badEvent_anti (g : ι → Finset α) (T : Finset ι) {S S' : Finset α}
    (hSS : S' ⊆ S) (hS : S ∈ noneOf (badEvent g) T) : S' ∈ noneOf (badEvent g) T := by
  rw [mem_noneOf] at hS ⊢
  intro j hj hj'
  exact hS j hj (badEvent_mono g j hSS hj')

lemma noneOf_union (A : ι → Finset (Finset α)) (N M : Finset ι) :
    noneOf A (N ∪ M) = noneOf A N ∩ noneOf A M := by
  ext S
  simp only [mem_noneOf, mem_inter, Finset.mem_union]
  exact ⟨fun h => ⟨fun j hj => h j (Or.inl hj), fun j hj => h j (Or.inr hj)⟩,
    fun h j hj => hj.elim (h.1 j) (h.2 j)⟩

/-- The per-step contraction factor: `1 - P(Aᵢ) + ∑_{j ∈ U, g j ∩ g i ≠ ∅} P(Aᵢ ∩ A_j)`. -/
def jansonFactor (p : α → ℝ) (g : ι → Finset α) (i : ι) (U : Finset ι) : ℝ :=
  1 - wprob (pweight p) (badEvent g i)
    + ∑ j ∈ U.filter (fun j => (g i ∩ g j).Nonempty),
        wprob (pweight p) (badEvent g i ∩ badEvent g j)

lemma jansonFactor_nonneg (p : α → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (g : ι → Finset α) (i : ι) (U : Finset ι) : 0 ≤ jansonFactor p g i U := by
  have hw : ∀ S, 0 ≤ pweight p S := fun S => pweight_nonneg hp0 hp1 S
  have hsumw : ∑ S : Finset α, pweight p S = 1 := by
    have h := sum_pweight (α := α) p
    rwa [Finset.powerset_univ] at h
  have h1 : wprob (pweight p) (badEvent g i) ≤ 1 := wprob_le_one hw hsumw _
  have h2 : 0 ≤ ∑ j ∈ U.filter (fun j => (g i ∩ g j).Nonempty),
      wprob (pweight p) (badEvent g i ∩ badEvent g j) :=
    Finset.sum_nonneg fun j _ => wprob_nonneg hw _
  rw [jansonFactor]
  linarith

/-- `1 + x ≤ exp x` turns the factor into the exponential form. -/
lemma jansonFactor_le_exp (p : α → ℝ) (g : ι → Finset α) (i : ι) (U : Finset ι) :
    jansonFactor p g i U
      ≤ Real.exp (-wprob (pweight p) (badEvent g i)
          + ∑ j ∈ U.filter (fun j => (g i ∩ g j).Nonempty),
              wprob (pweight p) (badEvent g i ∩ badEvent g j)) := by
  have h := Real.add_one_le_exp (-wprob (pweight p) (badEvent g i)
    + ∑ j ∈ U.filter (fun j => (g i ∩ g j).Nonempty),
        wprob (pweight p) (badEvent g i ∩ badEvent g j))
  rw [jansonFactor]
  linarith

/-- **The Janson step.** Adding one more bad set to the family contracts the probability by

`1 - P(Aᵢ) + ∑ P(Aᵢ ∩ A_j)`, the sum over the `j ∈ T` whose bad set meets `g i`.

It holds for **any** finite `T` with no ordering hypothesis: split `T` into the `j` whose
bad set meets `g i` — handled by mixed Harris, since `Aᵢ ∩ A_j` is increasing and "none of
`M` occurs" is decreasing — and those disjoint from it, handled by block independence, since
they live on the complementary coordinate block. -/
theorem janson_step (p : α → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (g : ι → Finset α) (i : ι) (T : Finset ι) :
    wprob (pweight p) (noneOf (badEvent g) (insert i T))
      ≤ jansonFactor p g i T * wprob (pweight p) (noneOf (badEvent g) T) := by
  classical
  rw [jansonFactor]
  have hw : ∀ S, 0 ≤ pweight p S := fun S => pweight_nonneg hp0 hp1 S
  set N := T.filter (fun j => (g i ∩ g j).Nonempty) with hNdef
  set M := T.filter (fun j => ¬ (g i ∩ g j).Nonempty) with hMdef
  set A := badEvent g with hAdef
  have hDsplit : noneOf A T = noneOf A N ∩ noneOf A M := by
    rw [← noneOf_union, hNdef, hMdef, Finset.filter_union_filter_not_eq]
  -- the far part is on the complementary block
  have hdetM : DeterminedBy ((univ : Finset α) \ g i) (noneOf A M) := by
    refine determinedBy_noneOf (fun j => determinedBy_badEvent g j) ?_
    intro j hj x hx
    rw [hMdef, mem_filter, Finset.not_nonempty_iff_eq_empty] at hj
    rw [mem_sdiff]
    refine ⟨mem_univ x, fun hxi => ?_⟩
    have hmem : x ∈ g i ∩ g j := mem_inter.mpr ⟨hxi, hx⟩
    rw [hj.2] at hmem
    exact notMem_empty x hmem
  have hindep : wprob (pweight p) (A i ∩ noneOf A M)
      = wprob (pweight p) (A i) * wprob (pweight p) (noneOf A M) :=
    sum_pweight_inter_of_determinedBy p (determinedBy_badEvent g i) hdetM
  -- the near part is covered by the union bound, each term controlled by mixed Harris
  have hcover : A i ∩ noneOf A M
      ⊆ (A i ∩ noneOf A T) ∪ N.biUnion (fun j => A i ∩ A j ∩ noneOf A M) := by
    intro S hS
    rw [mem_inter] at hS
    by_cases hN : S ∈ noneOf A N
    · have hT : S ∈ noneOf A T := by
        rw [hDsplit]
        exact mem_inter.mpr ⟨hN, hS.2⟩
      exact Finset.mem_union_left _ (mem_inter.mpr ⟨hS.1, hT⟩)
    · rw [mem_noneOf] at hN
      push_neg at hN
      obtain ⟨j, hjN, hjA⟩ := hN
      refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, hjN, ?_⟩)
      exact mem_inter.mpr ⟨mem_inter.mpr ⟨hS.1, hjA⟩, hS.2⟩
  have hharris : ∀ j ∈ N, wprob (pweight p) (A i ∩ A j ∩ noneOf A M)
      ≤ wprob (pweight p) (A i ∩ A j) * wprob (pweight p) (noneOf A M) := by
    intro j _
    refine wprob_pweight_anticorrelate p hp0 hp1 ?_ ?_
    · intro S T' hST hS
      rw [mem_inter] at hS ⊢
      exact ⟨badEvent_mono g i hST hS.1, badEvent_mono g j hST hS.2⟩
    · intro S T' hST hT'
      exact noneOf_badEvent_anti g M hST hT'
  have hunion : wprob (pweight p) (A i ∩ noneOf A M)
      ≤ wprob (pweight p) (A i ∩ noneOf A T)
        + ∑ j ∈ N, wprob (pweight p) (A i ∩ A j ∩ noneOf A M) :=
    wprob_le_of_subset_union hw hcover
  -- assemble: `κ · P(D_M) ≤ P(Aᵢ ∩ D)` with `κ` the bracketed quantity
  have hmono : wprob (pweight p) (noneOf A T) ≤ wprob (pweight p) (noneOf A M) :=
    wprob_mono hw (by rw [hDsplit]; exact Finset.inter_subset_right)
  have hkey : (wprob (pweight p) (A i)
        - ∑ j ∈ N, wprob (pweight p) (A i ∩ A j)) * wprob (pweight p) (noneOf A M)
      ≤ wprob (pweight p) (A i ∩ noneOf A T) := by
    have hsum : ∑ j ∈ N, wprob (pweight p) (A i ∩ A j ∩ noneOf A M)
        ≤ (∑ j ∈ N, wprob (pweight p) (A i ∩ A j)) * wprob (pweight p) (noneOf A M) := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum hharris
    rw [sub_mul]
    linarith [hindep, hunion, hsum]
  have hDnn : 0 ≤ wprob (pweight p) (noneOf A T) := wprob_nonneg hw _
  have hAiDnn : 0 ≤ wprob (pweight p) (A i ∩ noneOf A T) := wprob_nonneg hw _
  rw [hAdef, noneOf_insert, wprob_compl_inter]
  rcases le_total 0 (wprob (pweight p) (A i)
      - ∑ j ∈ N, wprob (pweight p) (A i ∩ A j)) with hκ | hκ
  · have := mul_le_mul_of_nonneg_left hmono hκ
    have hgoal : (wprob (pweight p) (A i)
          - ∑ j ∈ N, wprob (pweight p) (A i ∩ A j)) * wprob (pweight p) (noneOf A T)
        ≤ wprob (pweight p) (A i ∩ noneOf A T) := le_trans this hkey
    nlinarith [hgoal]
  · nlinarith [hκ, hDnn, hAiDnn]

end Upper

section UpperOrder

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- **The multiplicative upper bound.** Peel the largest index each time, so the set already
peeled is always a prefix — the same induction as `PMC.sum_chain_eq` in Chapter 10. -/
theorem janson_prod_le (p : α → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (g : ι → Finset α) (T : Finset ι) :
    wprob (pweight p) (noneOf (badEvent g) T)
      ≤ ∏ i ∈ T, jansonFactor p g i (T.filter fun j => j < i) := by
  classical
  have hw : ∀ S, 0 ≤ pweight p S := fun S => pweight_nonneg hp0 hp1 S
  have hsumw : ∑ S : Finset α, pweight p S = 1 := by
    have h := sum_pweight (α := α) p
    rwa [Finset.powerset_univ] at h
  induction T using Finset.strongInduction with
  | _ T ih =>
    rcases T.eq_empty_or_nonempty with rfl | hT
    · simp [noneOf_empty, wprob_univ, hsumw]
    · obtain ⟨m, hm, hmax⟩ := T.exists_max_image id hT
      have hpre : T.filter (fun j => j < m) = T.erase m := by
        ext x
        simp only [mem_filter, mem_erase]
        exact ⟨fun h => ⟨ne_of_lt h.2, h.1⟩,
          fun h => ⟨h.2, lt_of_le_of_ne (hmax x h.2) h.1⟩⟩
      have hterms : ∀ i ∈ T.erase m,
          T.filter (fun j => j < i) = (T.erase m).filter (fun j => j < i) := by
        intro i hi
        rw [mem_erase] at hi
        ext x
        simp only [mem_filter, mem_erase]
        refine ⟨fun h => ⟨⟨?_, h.1⟩, h.2⟩, fun h => ⟨h.1.2, h.2⟩⟩
        intro hxm
        exact absurd (hxm ▸ h.2) (not_lt_of_ge (hmax i hi.2))
      have hstep := janson_step p hp0 hp1 g m (T.erase m)
      rw [Finset.insert_erase hm] at hstep
      have hih := ih (T.erase m) (Finset.erase_ssubset hm)
      have hfnn : 0 ≤ jansonFactor p g m (T.erase m) := jansonFactor_nonneg p hp0 hp1 g m _
      calc wprob (pweight p) (noneOf (badEvent g) T)
          ≤ jansonFactor p g m (T.erase m)
              * wprob (pweight p) (noneOf (badEvent g) (T.erase m)) := hstep
        _ ≤ jansonFactor p g m (T.erase m)
              * ∏ i ∈ T.erase m, jansonFactor p g i ((T.erase m).filter fun j => j < i) :=
            mul_le_mul_of_nonneg_left hih hfnn
        _ = ∏ i ∈ T, jansonFactor p g i (T.filter fun j => j < i) := by
            rw [← Finset.mul_prod_erase _ _ hm, hpre]
            congr 1
            exact Finset.prod_congr rfl fun i hi => by rw [hterms i hi]

/-- **Janson's inequality — the upper bound** (Zhao, Theorem 8.1.1).

With `μ = ∑ P(Aᵢ)` the expected number of bad sets appearing, and the double sum below the
*lower-triangular* half of Zhao's `Δ` (so it equals `Δ / 2`),

`P(no bad set appears) ≤ exp (-μ + Δ/2)`.

Kept multiplicative throughout — no conditional probabilities, hence no case analysis on
whether a prefix has positive probability. -/
theorem janson_upper (p : α → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (g : ι → Finset α) :
    wprob (pweight p) (noneOf (badEvent g) (univ : Finset ι))
      ≤ Real.exp (-(∑ i, wprob (pweight p) (badEvent g i))
          + ∑ i, ∑ j ∈ ((univ : Finset ι).filter fun j => j < i).filter
              (fun j => (g i ∩ g j).Nonempty),
              wprob (pweight p) (badEvent g i ∩ badEvent g j)) := by
  classical
  calc wprob (pweight p) (noneOf (badEvent g) (univ : Finset ι))
      ≤ ∏ i : ι, jansonFactor p g i ((univ : Finset ι).filter fun j => j < i) :=
        janson_prod_le p hp0 hp1 g univ
    _ ≤ ∏ i : ι, Real.exp (-wprob (pweight p) (badEvent g i)
          + ∑ j ∈ ((univ : Finset ι).filter fun j => j < i).filter
              (fun j => (g i ∩ g j).Nonempty),
              wprob (pweight p) (badEvent g i ∩ badEvent g j)) :=
        Finset.prod_le_prod (fun i _ => jansonFactor_nonneg p hp0 hp1 g i _)
          (fun i _ => jansonFactor_le_exp p g i _)
    _ = Real.exp (∑ i, (-wprob (pweight p) (badEvent g i)
          + ∑ j ∈ ((univ : Finset ι).filter fun j => j < i).filter
              (fun j => (g i ∩ g j).Nonempty),
              wprob (pweight p) (badEvent g i ∩ badEvent g j))) := (Real.exp_sum ..).symm
    _ = Real.exp (-(∑ i, wprob (pweight p) (badEvent g i))
          + ∑ i, ∑ j ∈ ((univ : Finset ι).filter fun j => j < i).filter
              (fun j => (g i ∩ g j).Nonempty),
              wprob (pweight p) (badEvent g i ∩ badEvent g j)) := by
        congr 1
        rw [Finset.sum_add_distrib, ← Finset.sum_neg_distrib]

/-- **The lower-triangular double sum is exactly half of Zhao's `Δ`.**

The notes define `Δ = ∑_{i ∼ j} P(Aᵢ ∩ A_j)` over *ordered* pairs and state the bound as
`exp(-μ + Δ/2)`. Since the relation "share an element" is symmetric and
`P(Aᵢ ∩ A_j) = P(A_j ∩ Aᵢ)`, the ordered sum splits into the `j < i` and `i < j` halves and
the map `(i,j) ↦ (j,i)` matches them term by term. -/
theorem two_mul_sum_lt_eq_sum_ne (p : α → ℝ) (g : ι → Finset α) :
    2 * ∑ i : ι, ∑ j ∈ ((univ : Finset ι).filter fun j => j < i).filter
          (fun j => (g i ∩ g j).Nonempty),
          wprob (pweight p) (badEvent g i ∩ badEvent g j)
      = ∑ i : ι, ∑ j ∈ (univ : Finset ι).filter
          (fun j => j ≠ i ∧ (g i ∩ g j).Nonempty),
          wprob (pweight p) (badEvent g i ∩ badEvent g j) := by
  classical
  have hLif : ∀ i : ι, ∑ j ∈ ((univ : Finset ι).filter fun j => j < i).filter
        (fun j => (g i ∩ g j).Nonempty),
        wprob (pweight p) (badEvent g i ∩ badEvent g j)
      = ∑ j : ι, (if j < i ∧ (g i ∩ g j).Nonempty
          then wprob (pweight p) (badEvent g i ∩ badEvent g j) else 0) := by
    intro i
    rw [Finset.filter_filter, Finset.sum_filter]
  have hNif : ∀ i : ι, ∑ j ∈ (univ : Finset ι).filter
        (fun j => j ≠ i ∧ (g i ∩ g j).Nonempty),
        wprob (pweight p) (badEvent g i ∩ badEvent g j)
      = ∑ j : ι, (if j ≠ i ∧ (g i ∩ g j).Nonempty
          then wprob (pweight p) (badEvent g i ∩ badEvent g j) else 0) := by
    intro i
    rw [Finset.sum_filter]
  have hsplit : ∀ i j : ι, (if j ≠ i ∧ (g i ∩ g j).Nonempty
        then wprob (pweight p) (badEvent g i ∩ badEvent g j) else 0)
      = (if j < i ∧ (g i ∩ g j).Nonempty
          then wprob (pweight p) (badEvent g i ∩ badEvent g j) else 0)
        + (if i < j ∧ (g i ∩ g j).Nonempty
          then wprob (pweight p) (badEvent g i ∩ badEvent g j) else 0) := by
    intro i j
    rcases lt_trichotomy j i with h | h | h
    · simp [h, ne_of_lt h, asymm h]
    · simp [h]
    · simp [h, ne_of_gt h, asymm h]
  have hU : ∑ i : ι, ∑ j : ι, (if i < j ∧ (g i ∩ g j).Nonempty
        then wprob (pweight p) (badEvent g i ∩ badEvent g j) else 0)
      = ∑ i : ι, ∑ j : ι, (if j < i ∧ (g i ∩ g j).Nonempty
        then wprob (pweight p) (badEvent g i ∩ badEvent g j) else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.inter_comm (g y) (g x), Finset.inter_comm (badEvent g y) (badEvent g x)]
  rw [Finset.sum_congr rfl fun i _ => hNif i,
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hsplit i j]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib, Finset.sum_add_distrib, hU,
    Finset.sum_congr rfl fun i _ => hLif i]
  ring

lemma wprob_badEvent (p : α → ℝ) (g : ι → Finset α) (i : ι) :
    wprob (pweight p) (badEvent g i) = ∏ x ∈ g i, p x := by
  have h := sum_pweight_superset p (g i)
  rw [Finset.powerset_univ] at h
  rw [wprob, badEvent]
  exact h

lemma noneOf_badEvent_eq (g : ι → Finset α) :
    noneOf (badEvent g) (univ : Finset ι)
      = (univ : Finset (Finset α)).filter (fun S => ∀ i, ¬ g i ⊆ S) := by
  ext S
  simp [mem_noneOf]

/-- The lower bound restated in the same language as the upper one. -/
theorem janson_lower' (p : α → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (g : ι → Finset α) :
    ∏ i, (1 - wprob (pweight p) (badEvent g i))
      ≤ wprob (pweight p) (noneOf (badEvent g) (univ : Finset ι)) := by
  rw [noneOf_badEvent_eq, wprob, Finset.prod_congr rfl fun i _ => by rw [wprob_badEvent]]
  exact janson_lower p hp0 hp1 g

/-- **Janson's inequality** (Zhao, Theorem 8.1.1), both bounds, in the notes' form.

With `μ = ∑ P(Aᵢ)` and `Δ = ∑_{i ∼ j} P(Aᵢ ∩ A_j)` over *ordered* pairs of distinct indices
whose bad sets share an element,

`∏ (1 - P(Aᵢ))  ≤  P(no bad set appears)  ≤  exp (-μ + Δ/2)`.

The two halves have nothing in common as proofs. The lower bound is Harris' inequality —
decreasing events are positively correlated, so correlation only helps, and no hypothesis
relating the `g i` is needed. The upper bound peels the family one index at a time, using
block independence for the bad sets disjoint from the current one and mixed Harris for those
that meet it. -/
theorem janson (p : α → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (g : ι → Finset α) :
    ∏ i, (1 - wprob (pweight p) (badEvent g i))
        ≤ wprob (pweight p) (noneOf (badEvent g) (univ : Finset ι))
      ∧ wprob (pweight p) (noneOf (badEvent g) (univ : Finset ι))
        ≤ Real.exp (-(∑ i, wprob (pweight p) (badEvent g i))
            + (∑ i, ∑ j ∈ (univ : Finset ι).filter
                (fun j => j ≠ i ∧ (g i ∩ g j).Nonempty),
                wprob (pweight p) (badEvent g i ∩ badEvent g j)) / 2) := by
  refine ⟨janson_lower' p hp0 hp1 g, le_trans (janson_upper p hp0 hp1 g) (le_of_eq ?_)⟩
  rw [← two_mul_sum_lt_eq_sum_ne p g]
  congr 1
  ring

end UpperOrder

/-! ## §8.2 — Lower tails

Theorem 8.2.2 (Janson inequality III) bootstraps the upper bound of 8.1.1 into a lower-tail
estimate: with `μ` the expected number of bad sets appearing and `Δ` the overlap sum,

`P(X ≤ μ - t) ≤ exp (-t² / (2 (μ + Δ)))` for `0 ≤ t ≤ μ`.

Naming `μ`, `Δ` and the count `X` keeps the statement readable; `PMC.janson` above could be
restated in them too.
-/

section LowerTail

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The number of bad sets that appear in `S`. -/
def badCount (g : ι → Finset α) (S : Finset α) : ℕ :=
  #((univ : Finset ι).filter fun i => g i ⊆ S)

/-- `μ`: the expected number of bad sets that appear. -/
noncomputable def jansonMu (p : α → ℝ) (g : ι → Finset α) : ℝ :=
  ∑ i, wprob (pweight p) (badEvent g i)

/-- `Δ`: the sum of `P(Aᵢ ∩ A_j)` over *ordered* pairs of distinct bad sets that overlap —
Zhao's convention, so that 8.1.1's upper bound reads `exp (-μ + Δ/2)`. -/
noncomputable def jansonDelta (p : α → ℝ) (g : ι → Finset α) : ℝ :=
  ∑ i, ∑ j ∈ (univ : Finset ι).filter (fun j => j ≠ i ∧ (g i ∩ g j).Nonempty),
    wprob (pweight p) (badEvent g i ∩ badEvent g j)

/-- **Theorem 8.2.2 (Janson inequality III).** The lower tail. -/
theorem janson_lower_tail (p : α → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (g : ι → Finset α) {t : ℝ} (ht0 : 0 ≤ t) (htmu : t ≤ jansonMu p g) :
    ∑ S ∈ (univ : Finset (Finset α)).filter
        (fun S => (badCount g S : ℝ) ≤ jansonMu p g - t), pweight p S
      ≤ Real.exp (-t ^ 2 / (2 * (jansonMu p g + jansonDelta p g))) := by
  sorry

end LowerTail

end Janson

end PMC
