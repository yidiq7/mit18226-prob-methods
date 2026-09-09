import ProbMethods.Chapter06.Compactness
import Mathlib.Topology.Constructions
import Mathlib.Topology.Compactness.Compact

/-!
# §6.2 — Lemma 6.2.7, the compactness argument in the variable model

Zhao, *Probabilistic Methods in Combinatorics*, Lemma 6.2.7:

> Consider a variation of the random variable model (Setup 6.1.5) where each variable has only
> finitely many choices but there can be possibly infinitely many events (each event depends on
> a finite subset of variables). If it is possible to avoid any finite subset of events, then
> it is possible to avoid all the events.

`PMC.exists_avoid_all_of_avoid_finite` is exactly that, and it is the general form of the
argument `ProbMethods/Chapter06/Compactness.lean` runs for hypergraph colourings:
`PMC.exists_two_coloring_of_finite` is the case `C i = Bool`, one event per edge, depending on
that edge's vertices — and is re-derived from it below
(`PMC.exists_two_coloring_of_finite_of_avoid`).

## The hypotheses, and why they are the right ones

* **finitely many choices per variable** is `[∀ i, Finite (C i)]`, and it is what compactness
  needs: `∀ i, C i` carries the product of discrete finite topologies, compact by Tychonoff.
* **each event depends on a finite subset of the variables** is `dep j : Finset ι` together
  with `hdep`: if `x` and `y` agree on `dep j` then `bad j x → bad j y`. Stated as an
  implication rather than an equivalence because that is all the proof uses, and it is the
  weaker hypothesis (applying it both ways gives the equivalence anyway).
* **nonemptiness of the choice sets is not assumed** — it follows, since avoiding the *empty*
  set of events already produces a point.

Remark 6.2.8 in the notes points out that the conclusion can fail without the variable model.
The mechanism is visible here: what makes each `{x | ¬ bad j x}` *closed* is that `bad j`
factors through the restriction to the finite set `dep j`, whose codomain is a finite discrete
space. An event that genuinely depended on infinitely many variables would give a set that need
not be closed, and the intersection of the finite-stage solutions could be empty.
-/

open Finset

namespace PMC

section AvoidEvents

/-- **Lemma 6.2.7 (compactness argument).** Variables `i : ι` with finitely many choices each,
events `j : κ` with `bad j` depending only on the variables in the finite set `dep j`. If every
*finite* set of events can be avoided simultaneously, all of them can. -/
theorem exists_avoid_all_of_avoid_finite {ι κ : Type*} (C : ι → Type*) [∀ i, Finite (C i)]
    (bad : κ → (∀ i, C i) → Prop) (dep : κ → Finset ι)
    (hdep : ∀ j (x y : ∀ i, C i), (∀ i ∈ dep j, x i = y i) → bad j x → bad j y)
    (hfin : ∀ J : Finset κ, ∃ x : ∀ i, C i, ∀ j ∈ J, ¬ bad j x) :
    ∃ x : ∀ i, C i, ∀ j, ¬ bad j x := by
  classical
  letI : ∀ i, TopologicalSpace (C i) := fun _ => ⊥
  haveI : ∀ i, DiscreteTopology (C i) := fun _ => ⟨rfl⟩
  -- each event's bad set is *open* (indeed clopen): it factors through the restriction to
  -- `dep j`, whose codomain is a finite discrete space
  have hopen_bad : ∀ j, IsOpen {x : ∀ i, C i | bad j x} := by
    intro j
    set res : (∀ i, C i) → (∀ i : {i // i ∈ dep j}, C i) := fun x i => x i.1 with hres
    have hcont : Continuous res := continuous_pi fun i => continuous_apply _
    have himg : {x : ∀ i, C i | bad j x} = res ⁻¹' (res '' {x | bad j x}) := by
      refine Set.Subset.antisymm (Set.subset_preimage_image _ _) ?_
      intro x hx
      obtain ⟨y, hy, hxy⟩ := hx
      refine hdep j y x (fun i hi => ?_) hy
      exact congrFun hxy ⟨i, hi⟩
    rw [himg]
    exact IsOpen.preimage hcont (isOpen_discrete _)
  -- the sets of points avoiding a finite stage
  set good : Finset κ → Set (∀ i, C i) := fun J => {x | ∀ j ∈ J, ¬ bad j x} with hgood
  have hclosed : ∀ J, IsClosed (good J) := by
    intro J
    have : good J = ⋂ j ∈ J, {x : ∀ i, C i | bad j x}ᶜ := by
      ext x
      simp [hgood, Set.mem_iInter]
    rw [this]
    exact isClosed_biInter fun j _ => (hopen_bad j).isClosed_compl
  have hne : ∀ J, (good J).Nonempty := fun J => (hfin J).imp fun _ hx => hx
  have hdir : Directed (· ⊇ ·) good := by
    intro J K
    refine ⟨J ∪ K, ?_, ?_⟩
    · exact fun x hx j hj => hx j (Finset.mem_union_left _ hj)
    · exact fun x hx j hj => hx j (Finset.mem_union_right _ hj)
  obtain ⟨x, hx⟩ :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed good hdir hne
      (fun J => (hclosed J).isCompact) hclosed
  exact ⟨x, fun j => Set.mem_iInter.mp hx {j} j (mem_singleton_self j)⟩

/-- **The hypergraph colouring case.** `PMC.exists_two_coloring_of_finite` — the compactness
step of Theorem 6.2.6 — is Lemma 6.2.7 with two choices per variable (`Bool`), one event per
edge, and `dep i = edge i`.

The only translation needed is between the two ways of indexing the finite stages: the notes'
colouring statement quantifies over finite sets of *vertices*, Lemma 6.2.7 over finite sets of
*events*, and `X := J.biUnion edge` converts one into the other. -/
theorem exists_two_coloring_of_avoid {V ι : Type*} [DecidableEq V] (edge : ι → Finset V)
    (hfin : ∀ X : Finset V, ∃ c : V → Bool, ∀ i, edge i ⊆ X → Bichromatic edge c i) :
    ∃ c : V → Bool, ∀ i, Bichromatic edge c i := by
  classical
  have hdep : ∀ (i : ι) (c d : V → Bool), (∀ v ∈ edge i, c v = d v) →
      ¬ Bichromatic edge c i → ¬ Bichromatic edge d i := by
    intro i c d hcd hc hd
    obtain ⟨u, hu, v, hv, huv⟩ := hd
    exact hc ⟨u, hu, v, hv, by rw [hcd u hu, hcd v hv]; exact huv⟩
  have hstage : ∀ J : Finset ι, ∃ c : V → Bool, ∀ i ∈ J, ¬ ¬ Bichromatic edge c i := by
    intro J
    obtain ⟨c, hc⟩ := hfin (J.biUnion edge)
    refine ⟨c, fun i hi => not_not_intro (hc i ?_)⟩
    exact fun v hv => Finset.mem_biUnion.mpr ⟨i, hi, hv⟩
  obtain ⟨c, hc⟩ :=
    exists_avoid_all_of_avoid_finite (fun _ : V => Bool)
      (fun i c => ¬ Bichromatic edge c i) edge hdep hstage
  exact ⟨c, fun i => not_not.mp (hc i)⟩

end AvoidEvents

end PMC
