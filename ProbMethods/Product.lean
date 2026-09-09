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

end Product

end PMC
