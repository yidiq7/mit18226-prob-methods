import ProbMethods.Basic

/-!
# §1.4 — List chromatic number of `K_{n,n}`

Zhao, *Probabilistic Methods in Combinatorics*, Theorems 1.4.2 and 1.4.3.
-/

open Finset

namespace PMC

/-- **`K_{n,n}` is `k`-choosable when `n < 2 ^ (k - 1)`** (Zhao, Theorem 1.4.2).

Equivalently `ch(K_{n,n}) ≤ ⌊log₂ (2n)⌋ + 1`.

The book's proof marks each colour `L` or `R` independently and uniformly at random, then
deletes the `R`-marked colours from the lists on the left side and the `L`-marked colours
from the lists on the right. A vertex is left with an empty list with probability `2 ^ (-k)`,
so by the union bound some marking leaves every one of the `2n` vertices a usable colour;
choosing from the surviving lists uses each colour on one side only. -/
theorem completeBipartiteChoosable_of_lt_two_pow {n k : ℕ} (hn : n < 2 ^ (k - 1)) :
    CompleteBipartiteChoosable n k := by
  sorry

/-- **Non-2-colourable hypergraphs obstruct choosability** (Zhao, Theorem 1.4.3).

If some `k`-uniform hypergraph with `n` edges is not 2-colourable, then `K_{n,n}` is not
`k`-choosable.

The book's proof views the vertex set of the hypergraph as the colour set, and gives the
`i`-th vertex on each side of `K_{n,n}` the list consisting of the `i`-th edge. A proper
list colouring would then 2-colour the hypergraph. -/
theorem not_completeBipartiteChoosable_of_not_twoColorable {n k : ℕ}
    {V : Type} [Fintype V] [DecidableEq V] {E : Finset (Finset V)}
    (hk : ∀ e ∈ E, #e = k) (hcard : #E = n) (hE : ¬ TwoColorable E) :
    ¬ CompleteBipartiteChoosable n k := by
  intro hch
  refine hE ?_
  -- Read the hypergraph's vertices as colours, transported along an injection into `ℕ`.
  obtain ⟨φ, hφ⟩ : ∃ φ : V → ℕ, Function.Injective φ :=
    ⟨fun x => (Fintype.equivFin V x : ℕ),
      fun x y h => (Fintype.equivFin V).injective (Fin.val_inj.1 h)⟩
  -- Enumerate the `n` edges. The enumeration is onto, so every edge is some `edge i`.
  obtain ⟨edge, hedgeE, hedgeonto⟩ :
      ∃ edge : Fin n → Finset V, (∀ i, edge i ∈ E) ∧ ∀ e ∈ E, ∃ i, edge i = e := by
    refine ⟨fun i => ((Finset.equivFinOfCardEq hcard).symm i : Finset V),
      fun i => ((Finset.equivFinOfCardEq hcard).symm i).2, fun e he => ?_⟩
    exact ⟨Finset.equivFinOfCardEq hcard ⟨e, he⟩, by simp⟩
  -- Vertex `i` on either side of `K_{n,n}` gets the `i`-th edge as its list of colours.
  obtain ⟨L, hLl, hLr⟩ :
      ∃ L : Fin n ⊕ Fin n → Finset ℕ,
        (∀ i, L (Sum.inl i) = (edge i).image φ) ∧
        (∀ i, L (Sum.inr i) = (edge i).image φ) :=
    ⟨Sum.elim (fun i => (edge i).image φ) (fun i => (edge i).image φ),
      fun _ => rfl, fun _ => rfl⟩
  have hLcard : ∀ v, #(L v) = k := by
    rintro (i | i)
    · rw [hLl, card_image_of_injective _ hφ]; exact hk _ (hedgeE i)
    · rw [hLr, card_image_of_injective _ hφ]; exact hk _ (hedgeE i)
  obtain ⟨f, hf1, hf2⟩ := hch L hLcard
  -- Colour a vertex `true` exactly when the left side of `K_{n,n}` uses it.
  refine ⟨fun u => decide (∃ i, f (Sum.inl i) = φ u), fun e he => ?_⟩
  obtain ⟨i, rfl⟩ := hedgeonto e he
  have hfu : f (Sum.inl i) ∈ (edge i).image φ := by rw [← hLl i]; exact hf1 (Sum.inl i)
  have hfv : f (Sum.inr i) ∈ (edge i).image φ := by rw [← hLr i]; exact hf1 (Sum.inr i)
  obtain ⟨u, hu, hueq⟩ := mem_image.1 hfu
  obtain ⟨v, hv, hveq⟩ := mem_image.1 hfv
  refine ⟨u, hu, v, hv, ?_⟩
  -- `u` is used on the left by construction; `v` cannot be, since no colour is used on
  -- both sides. So this edge is not monochromatic.
  have hut : ∃ i', f (Sum.inl i') = φ u := ⟨i, hueq.symm⟩
  have hvf : ¬ ∃ i', f (Sum.inl i') = φ v := by
    rintro ⟨i', hi'⟩
    exact hf2 i' i (hi'.trans hveq)
  simp only [ne_eq, decide_eq_decide]
  exact fun hiff => hvf (hiff.1 hut)

end PMC
