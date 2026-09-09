import ProbMethods.Weighted

/-!
# Product sample spaces

`ProbMethods/Weighted.lean` handles events on `Finset α` — a random *subset*, each element
kept independently. Several arguments in Chapter 6 instead choose one value per coordinate:
§6.4 colours the vertices from `ZMod k`, §6.3 picks one vertex from each part. Their sample
space is a product `ι → β`, not a powerset, and `PMC.DeterminedBy` does not apply.

This file supplies the product analogue. The whole content is `PMC.spliceOn`: given two
points of the product, take the coordinates in `C` from one and the rest from the other.
Splicing is an **involution on pairs** — `(f, g) ↦ (splice f g, splice g f)` applied twice
is the identity — and that single observation gives block independence
(`PMC.card_inter_mul_of_determinedOn`) with no case analysis and no subtypes.

Avoiding subtypes is deliberate. The obvious route, `(ι → β) ≃ (C → β) × (Cᶜ → β)`, drags
dependent types through every step; splicing keeps every object at type `ι → β`. It is the
same choice that `PMC.masked` made for Chapter 10's tuples.
-/

open Finset

namespace PMC

section Product

variable {ι β : Type*} [DecidableEq ι]

/-- Take the coordinates in `C` from `f` and the rest from `g`. -/
def spliceOn (C : Finset ι) (f g : ι → β) : ι → β := fun i => if i ∈ C then f i else g i

@[simp] lemma spliceOn_of_mem {C : Finset ι} {f g : ι → β} {i : ι} (hi : i ∈ C) :
    spliceOn C f g i = f i := by simp [spliceOn, hi]

@[simp] lemma spliceOn_of_notMem {C : Finset ι} {f g : ι → β} {i : ι} (hi : i ∉ C) :
    spliceOn C f g i = g i := by simp [spliceOn, hi]

/-- **Splicing is an involution on pairs.** This is the only computation the whole file
needs, and it is why no case analysis appears later. -/
lemma spliceOn_spliceOn (C : Finset ι) (f g : ι → β) :
    spliceOn C (spliceOn C f g) (spliceOn C g f) = f := by
  funext i
  by_cases hi : i ∈ C <;> simp [hi]

/-- An event on the product space is *determined on* `C` when membership depends only on
the coordinates in `C`. -/
def DeterminedOn (C : Finset ι) (A : Finset (ι → β)) : Prop :=
  ∀ f g : ι → β, (∀ i ∈ C, f i = g i) → (f ∈ A ↔ g ∈ A)

lemma DeterminedOn.mono {C C' : Finset ι} {A : Finset (ι → β)} (h : C ⊆ C')
    (hA : DeterminedOn C A) : DeterminedOn C' A :=
  fun f g hfg => hA f g fun i hi => hfg i (h hi)

lemma DeterminedOn.inter {C : Finset ι} {A B : Finset (ι → β)} [DecidableEq (ι → β)]
    (hA : DeterminedOn C A) (hB : DeterminedOn C B) : DeterminedOn C (A ∩ B) := by
  intro f g hfg
  rw [mem_inter, mem_inter, hA f g hfg, hB f g hfg]

lemma DeterminedOn.compl {C : Finset ι} {A : Finset (ι → β)} [Fintype (ι → β)]
    [DecidableEq (ι → β)] (hA : DeterminedOn C A) : DeterminedOn C Aᶜ := by
  intro f g hfg
  rw [mem_compl, mem_compl, hA f g hfg]

@[simp] lemma determinedOn_univ_event (C : Finset ι) [Fintype (ι → β)] :
    DeterminedOn C (univ : Finset (ι → β)) := fun f g _ => by simp

variable [Fintype ι] [Fintype β] [DecidableEq β]

/-- **Events determined by disjoint blocks of coordinates are independent** (counting form).

`#(A ∩ B) · |ι → β| = #A · #B`, i.e. `P(A ∩ B) = P(A) P(B)` under the uniform measure on the
product. The proof is the splice involution: it identifies `A ×ˢ B` with
`(A ∩ B) ×ˢ univ`, since taking the `C`-coordinates from a point of `A` and the rest from a
point of `B` lands in both. -/
theorem card_inter_mul_of_determinedOn {C : Finset ι} {A B : Finset (ι → β)}
    (hA : DeterminedOn C A) (hB : DeterminedOn ((univ : Finset ι) \ C) B) :
    #(A ∩ B) * Fintype.card (ι → β) = #A * #B := by
  classical
  have hmaps : ∀ (X Y : Finset (ι → β)), (∀ f ∈ X, ∀ g ∈ Y, spliceOn C f g ∈ A) →
      True := fun _ _ _ => trivial
  -- `splice f g` agrees with `f` on `C` and with `g` off `C`
  have hinA : ∀ f g : ι → β, f ∈ A → spliceOn C f g ∈ A := by
    intro f g hf
    exact (hA f (spliceOn C f g) fun i hi => (spliceOn_of_mem hi).symm).mp hf
  have hinB : ∀ f g : ι → β, g ∈ B → spliceOn C f g ∈ B := by
    intro f g hg
    refine (hB g (spliceOn C f g) fun i hi => ?_).mp hg
    exact (spliceOn_of_notMem (mem_sdiff.mp hi).2).symm
  have hcard : #(A ×ˢ B) = #((A ∩ B) ×ˢ (univ : Finset (ι → β))) := by
    refine Finset.card_nbij' (fun q => (spliceOn C q.1 q.2, spliceOn C q.2 q.1))
      (fun q => (spliceOn C q.1 q.2, spliceOn C q.2 q.1)) ?_ ?_ ?_ ?_
    · intro q hq
      rw [mem_coe, Finset.mem_product] at hq
      rw [mem_coe, Finset.mem_product]
      exact ⟨mem_inter.mpr ⟨hinA q.1 q.2 hq.1, hinB q.1 q.2 hq.2⟩, mem_univ _⟩
    · intro q hq
      rw [mem_coe, Finset.mem_product, mem_inter] at hq
      rw [mem_coe, Finset.mem_product]
      refine ⟨hinA q.1 q.2 hq.1.1, ?_⟩
      -- `splice q.2 q.1` agrees with `q.1` off `C`, and `q.1 ∈ B`
      refine (hB q.1 (spliceOn C q.2 q.1) fun i hi => ?_).mp hq.1.2
      exact (spliceOn_of_notMem (mem_sdiff.mp hi).2).symm
    · intro q _
      exact Prod.ext (spliceOn_spliceOn C q.1 q.2) (spliceOn_spliceOn C q.2 q.1)
    · intro q _
      exact Prod.ext (spliceOn_spliceOn C q.1 q.2) (spliceOn_spliceOn C q.2 q.1)
  rw [Finset.card_product, Finset.card_product, card_univ] at hcard
  omega

/-- The uniform weight on the product space. -/
noncomputable def unifProd (ι β : Type*) [DecidableEq ι] [Fintype ι] [Fintype β] :
    (ι → β) → ℝ := fun _ => 1 / Fintype.card (ι → β)

lemma unifProd_apply (f : ι → β) :
    unifProd ι β f = 1 / Fintype.card (ι → β) := rfl

lemma unifProd_nonneg (f : ι → β) : 0 ≤ unifProd ι β f := by
  rw [unifProd_apply]; positivity

lemma sum_unifProd [Nonempty β] : ∑ f : ι → β, unifProd ι β f = 1 := by
  have hpos : (0 : ℝ) < Fintype.card (ι → β) := by
    have := Fintype.card_pos (α := ι → β)
    exact_mod_cast this
  rw [Finset.sum_congr rfl fun f _ => unifProd_apply f, Finset.sum_const, card_univ,
    nsmul_eq_mul, mul_one_div, div_self (ne_of_gt hpos)]

lemma wprob_unifProd (A : Finset (ι → β)) :
    wprob (unifProd ι β) A = #A / Fintype.card (ι → β) := by
  rw [wprob, Finset.sum_congr rfl fun f _ => unifProd_apply f, Finset.sum_const,
    nsmul_eq_mul, mul_one_div]

/-- **Block independence in probability form**, ready for the local lemma's `hindep`. -/
theorem wprob_unifProd_mul_of_determinedOn [Nonempty β] {C : Finset ι}
    {A B : Finset (ι → β)} (hA : DeterminedOn C A)
    (hB : DeterminedOn ((univ : Finset ι) \ C) B) :
    wprob (unifProd ι β) (A ∩ B)
      = wprob (unifProd ι β) A * wprob (unifProd ι β) B := by
  classical
  have hpos : (0 : ℝ) < Fintype.card (ι → β) := by
    have := Fintype.card_pos (α := ι → β)
    exact_mod_cast this
  have h : (#(A ∩ B) : ℝ) * Fintype.card (ι → β) = #A * #B := by
    exact_mod_cast card_inter_mul_of_determinedOn hA hB
  rw [wprob_unifProd, wprob_unifProd, wprob_unifProd, div_mul_div_comm,
    div_eq_div_iff (by positivity) (by positivity)]
  calc (#(A ∩ B) : ℝ) * (Fintype.card (ι → β) * Fintype.card (ι → β))
      = (#(A ∩ B) * Fintype.card (ι → β)) * Fintype.card (ι → β) := by ring
    _ = #A * #B * Fintype.card (ι → β) := by rw [h]

/-! ### Coordinates are uniform

Every application of `PMC.exists_avoiding_of_lll` has to compute the probability of an event
that pins down a few coordinates. `PMC.wprob_unifProd_coord` does one coordinate; block
independence (`PMC.wprob_unifProd_mul_of_determinedOn`) then multiplies them.

The fibres of `f ↦ f i` all have the same size, and the bijection between two of them is
`Function.update` — replacing the `i`-th coordinate, which is an involution up to swapping
the two values.
-/

/-- All fibres of a coordinate have the same size. -/
theorem card_filter_coord (i : ι) (a a' : β) :
    #((univ : Finset (ι → β)).filter fun f => f i = a)
      = #((univ : Finset (ι → β)).filter fun f => f i = a') := by
  classical
  refine Finset.card_nbij' (fun f => Function.update f i a')
    (fun f => Function.update f i a) ?_ ?_ ?_ ?_
  · intro f _
    rw [mem_coe, mem_filter]
    exact ⟨mem_univ _, Function.update_self i a' f⟩
  · intro f _
    rw [mem_coe, mem_filter]
    exact ⟨mem_univ _, Function.update_self i a f⟩
  · intro f hf
    rw [mem_coe, mem_filter] at hf
    funext x
    rcases eq_or_ne x i with rfl | hx
    · simp [Function.update_apply, hf.2]
    · simp [Function.update_apply, hx]
  · intro f hf
    rw [mem_coe, mem_filter] at hf
    funext x
    rcases eq_or_ne x i with rfl | hx
    · simp [Function.update_apply, hf.2]
    · simp [Function.update_apply, hx]

/-- The `#β` fibres partition the product, so each has size `card (ι → β) / #β`. -/
theorem card_filter_coord_mul (i : ι) (a : β) :
    #((univ : Finset (ι → β)).filter fun f => f i = a) * Fintype.card β
      = Fintype.card (ι → β) := by
  classical
  have hfib : ∑ b : β, #((univ : Finset (ι → β)).filter fun f => f i = b)
      = Fintype.card (ι → β) := by
    rw [← card_univ]
    exact (Finset.card_eq_sum_card_fiberwise (fun f _ => mem_univ (f i))).symm
  rw [← hfib, Finset.sum_congr rfl fun b _ => (card_filter_coord i a b).symm,
    Finset.sum_const, card_univ, smul_eq_mul, mul_comm]

/-- **Fixing one coordinate has probability `1 / #β`.** -/
theorem wprob_unifProd_coord [Nonempty β] (i : ι) (a : β) :
    wprob (unifProd ι β) ((univ : Finset (ι → β)).filter fun f => f i = a)
      = 1 / Fintype.card β := by
  classical
  have hβ : (0 : ℝ) < Fintype.card β := by
    have := Fintype.card_pos (α := β)
    exact_mod_cast this
  have hmul := card_filter_coord_mul (ι := ι) i a
  have hne : (0 : ℝ) < #((univ : Finset (ι → β)).filter fun f => f i = a) := by
    have : (fun _ => a) ∈ (univ : Finset (ι → β)).filter fun f => f i = a := by
      rw [mem_filter]
      exact ⟨mem_univ _, rfl⟩
    have hpos := Finset.card_pos.mpr ⟨_, this⟩
    exact_mod_cast hpos
  rw [wprob_unifProd]
  rw [show (Fintype.card (ι → β) : ℝ)
      = #((univ : Finset (ι → β)).filter fun f => f i = a) * Fintype.card β from by
    exact_mod_cast hmul.symm]
  rw [← div_div, div_self (ne_of_gt hne)]

/-- **A predicate on one coordinate.** The single-value case
`PMC.wprob_unifProd_coord` summed over the values the predicate allows. -/
theorem wprob_unifProd_coord_pred [Nonempty β] (i : ι) (P : β → Prop) [DecidablePred P] :
    wprob (unifProd ι β) ((univ : Finset (ι → β)).filter fun f => P (f i))
      = #((univ : Finset β).filter P) / Fintype.card β := by
  classical
  have hβ : (0 : ℝ) < Fintype.card β := by
    have := Fintype.card_pos (α := β)
    exact_mod_cast this
  have hprod : (0 : ℝ) < Fintype.card (ι → β) := by
    have := Fintype.card_pos (α := ι → β)
    exact_mod_cast this
  -- count in `ℕ` first: the fibres over the allowed values
  have hnat : #((univ : Finset (ι → β)).filter fun f => P (f i)) * Fintype.card β
      = #((univ : Finset β).filter P) * Fintype.card (ι → β) := by
    have hfib : #((univ : Finset (ι → β)).filter fun f => P (f i))
        = ∑ a ∈ (univ : Finset β).filter P,
            #((univ : Finset (ι → β)).filter fun f => f i = a) := by
      have h0 := Finset.card_eq_sum_card_fiberwise
        (s := (univ : Finset (ι → β)).filter fun f => P (f i))
        (f := fun f => f i) (t := (univ : Finset β).filter P) (fun f hf => by
          simp only [mem_coe, mem_filter, mem_univ, true_and] at hf ⊢
          exact hf)
      rw [h0]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [mem_filter] at ha
      congr 1
      ext f
      simp only [mem_filter, mem_univ, true_and]
      exact ⟨fun h => h.2, fun h => ⟨h ▸ ha.2, h⟩⟩
    rw [hfib, Finset.sum_mul,
      Finset.sum_congr rfl fun a _ => card_filter_coord_mul (ι := ι) i a,
      Finset.sum_const, smul_eq_mul]
  have hcast : (#((univ : Finset (ι → β)).filter fun f => P (f i)) : ℝ) * Fintype.card β
      = #((univ : Finset β).filter P) * Fintype.card (ι → β) := by exact_mod_cast hnat
  rw [wprob_unifProd, div_eq_div_iff (ne_of_gt hprod) (ne_of_gt hβ)]
  exact hcast

/-- **Independent coordinates multiply.** An event constraining each coordinate in `C`
separately has probability the product of the per-coordinate probabilities.

This is what an application with events on more than two coordinates needs — §6.4's bad
event constrains a vertex's whole out-neighbourhood. -/
theorem wprob_unifProd_forall [Nonempty β] (C : Finset ι) (P : ι → β → Prop)
    [∀ i, DecidablePred (P i)] :
    wprob (unifProd ι β) ((univ : Finset (ι → β)).filter fun f => ∀ i ∈ C, P i (f i))
      = ∏ i ∈ C, (#((univ : Finset β).filter (P i)) : ℝ) / Fintype.card β := by
  classical
  induction C using Finset.induction_on with
  | empty =>
      rw [Finset.prod_empty]
      have : ((univ : Finset (ι → β)).filter fun f => ∀ i ∈ (∅ : Finset ι), P i (f i))
          = univ := by
        ext f
        simp
      rw [this, wprob_univ, sum_unifProd]
  | @insert i C hi ih =>
      have hsplit : ((univ : Finset (ι → β)).filter fun f => ∀ j ∈ insert i C, P j (f j))
          = ((univ : Finset (ι → β)).filter fun f => P i (f i))
            ∩ ((univ : Finset (ι → β)).filter fun f => ∀ j ∈ C, P j (f j)) := by
        ext f
        simp only [mem_filter, mem_univ, true_and, mem_inter, Finset.forall_mem_insert]
      have hdet1 : DeterminedOn ({i} : Finset ι)
          ((univ : Finset (ι → β)).filter fun f => P i (f i)) := by
        intro f g hfg
        simp only [mem_filter, mem_univ, true_and]
        rw [hfg i (by simp)]
      have hdet2 : DeterminedOn ((univ : Finset ι) \ {i})
          ((univ : Finset (ι → β)).filter fun f => ∀ j ∈ C, P j (f j)) := by
        intro f g hfg
        simp only [mem_filter, mem_univ, true_and]
        have hEq : ∀ j ∈ C, f j = g j := fun j hj => hfg j (by
          rw [mem_sdiff, Finset.mem_singleton]
          exact ⟨mem_univ j, fun hji => hi (hji ▸ hj)⟩)
        constructor
        · intro h j hj
          rw [← hEq j hj]
          exact h j hj
        · intro h j hj
          rw [hEq j hj]
          exact h j hj
      rw [hsplit, wprob_unifProd_mul_of_determinedOn hdet1 hdet2,
        wprob_unifProd_coord_pred, ih, Finset.prod_insert hi]

end Product

end PMC
