import ProbMethods.Chapter06.LocalLemma
import ProbMethods.Product

/-!
# §6.3–§6.5 — the local lemma on a product sample space

§6.2 could run the local lemma on `Finset V`, because a 2-colouring *is* a subset and
`PMC.DeterminedBy` applies. The remaining applications choose one value per coordinate —
§6.3 one vertex from each part of a partition, §6.4 a label in `ZMod k` for each vertex — so
their sample space is a product `ι → β`.

`PMC.exists_avoiding_of_lll` is the local lemma packaged for that setting: supply the events,
the block of coordinates each one depends on, a bound `p` on their probabilities and a bound
`d` on how many other blocks each block meets, and it returns a point of the product avoiding
every event. Independence is discharged internally from
`PMC.wprob_unifProd_mul_of_determinedOn`, so an application never has to mention `wprob`.

This is the product-space twin of §6.2's `PMC.exists_two_coloring_of_local_lemma`, and the
three remaining Chapter 6 applications all go through it.
-/

open Finset

namespace PMC

section ProductLLL

variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The product analogue of `PMC.determinedBy_noneOf`: "none of the events in `T` occurs"
depends only on a block containing all of their blocks. -/
theorem determinedOn_noneOf {A : κ → Finset (ι → β)} {C : κ → Finset ι}
    (hA : ∀ c, DeterminedOn (C c) (A c)) {D : Finset ι} {T : Finset κ}
    (hT : ∀ c ∈ T, C c ⊆ D) : DeterminedOn D (noneOf A T) := by
  classical
  revert hT
  induction T using Finset.induction_on with
  | empty =>
      intro _
      simpa using determinedOn_univ_event (β := β) D
  | @insert c T _ ih =>
      intro hT
      rw [noneOf_insert]
      exact ((hA c).mono (hT c (mem_insert_self c T))).compl.inter
        (ih fun c' hc' => hT c' (mem_insert_of_mem hc'))

variable [Nonempty β]

/-- **The Lovász local lemma on a product sample space.**

Each event `A c` depends only on the coordinates in `C c`; events whose blocks are disjoint
are genuinely independent, which is what `hfar` records. Given `e p (d+1) ≤ 1`, some point of
the product avoids every event. -/
theorem exists_avoiding_of_lll (A : κ → Finset (ι → β)) (C : κ → Finset ι)
    (hA : ∀ c, DeterminedOn (C c) (A c))
    (N : κ → Finset κ) {d : ℕ} (hd : 0 < d) {p : ℝ} (hp0 : 0 ≤ p)
    (hself : ∀ c, c ∉ N c)
    (hdeg : ∀ c, #(N c) ≤ d)
    (hfar : ∀ c c' : κ, c' ∉ insert c (N c) → Disjoint (C c) (C c'))
    (hprob : ∀ c, wprob (unifProd ι β) (A c) ≤ p)
    (hep : Real.exp 1 * p * (d + 1) ≤ 1) :
    ∃ f : ι → β, ∀ c, f ∉ A c := by
  classical
  have hindep : ∀ (c : κ) (T : Finset κ), Disjoint T (insert c (N c)) →
      wprob (unifProd ι β) (A c ∩ noneOf A T)
        = wprob (unifProd ι β) (A c) * wprob (unifProd ι β) (noneOf A T) := by
    intro c T hT
    refine wprob_unifProd_mul_of_determinedOn (hA c) ?_
    refine determinedOn_noneOf hA ?_
    intro c' hc' i hi
    have hdis : Disjoint (C c) (C c') := hfar c c' (Finset.disjoint_left.mp hT hc')
    rw [mem_sdiff]
    exact ⟨mem_univ i, fun hic => Finset.disjoint_left.mp hdis hic hi⟩
  have hpos := lovasz_local_lemma_symmetric (unifProd ι β) unifProd_nonneg sum_unifProd
    A N hd hp0 hself hdeg hindep hprob hep
  have hne : (noneOf A (univ : Finset κ)).Nonempty := by
    rcases Finset.eq_empty_or_nonempty (noneOf A (univ : Finset κ)) with h | h
    · rw [h, wprob_empty] at hpos
      linarith
    · exact h
  obtain ⟨f, hf⟩ := hne
  exact ⟨f, fun c => mem_noneOf.mp hf c (mem_univ c)⟩

end ProductLLL

end PMC
