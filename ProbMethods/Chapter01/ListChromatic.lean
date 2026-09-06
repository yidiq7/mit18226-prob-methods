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
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · -- `K_{0,0}` has no vertices, so any `f` witnesses the conclusion vacuously.
    intro L _
    refine ⟨fun _ => 0, ?_, ?_⟩
    · rintro (i | i) <;> exact i.elim0
    · exact fun i => i.elim0
  intro L hL
  -- `k = 0` would force `n = 0`, which `hn0` rules out, so the lists are nonempty.
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have h1 : (2 : ℕ) ^ (0 - 1) = 1 := rfl
      omega
    · exact hk
  -- Only the colours that actually occur matter; collect them into a ground set `C`.
  obtain ⟨C, hsub⟩ : ∃ C : Finset ℕ, ∀ v, L v ⊆ C :=
    ⟨univ.biUnion L, fun v => subset_biUnion_of_mem L (mem_univ v)⟩
  have hkC : k ≤ #C := by
    have h := card_le_card (hsub (Sum.inl ⟨0, hn0⟩))
    rwa [hL] at h
  -- A marking is a `T ⊆ C`, read as the colours reserved for the left side. Left vertex
  -- `i` is starved when `T` misses its list entirely; right vertex `j` is starved when
  -- `T` swallows its list entirely.
  obtain ⟨bad, hbadL, hbadR⟩ :
      ∃ bad : Fin n ⊕ Fin n → Finset (Finset ℕ),
        (∀ i, bad (Sum.inl i) = {T ∈ C.powerset | L (Sum.inl i) ∩ T = ∅}) ∧
        (∀ j, bad (Sum.inr j) = {T ∈ C.powerset | L (Sum.inr j) ⊆ T}) :=
    ⟨Sum.elim (fun i => {T ∈ C.powerset | L (Sum.inl i) ∩ T = ∅})
      (fun j => {T ∈ C.powerset | L (Sum.inr j) ⊆ T}), fun _ => rfl, fun _ => rfl⟩
  -- Each vertex is starved by at most `2 ^ (#C - k)` of the `2 ^ #C` markings.
  have hpow : ∀ v, #((C \ L v).powerset) = 2 ^ (#C - k) := fun v => by
    rw [card_powerset, card_sdiff_of_subset (hsub v), hL]
  have hbadcard : ∀ v, #(bad v) ≤ 2 ^ (#C - k) := by
    rintro (i | j)
    · -- A marking missing `L (inl i)` is a subset of `C \ L (inl i)`.
      rw [hbadL, ← hpow (Sum.inl i)]
      refine card_le_card fun T hT => ?_
      rw [mem_filter, mem_powerset] at hT
      rw [mem_powerset]
      intro x hx
      refine mem_sdiff.2 ⟨hT.1 hx, fun hxL => ?_⟩
      have hmem : x ∈ L (Sum.inl i) ∩ T := mem_inter.2 ⟨hxL, hx⟩
      rw [hT.2] at hmem
      exact notMem_empty x hmem
    · -- `T ↦ T \ L (inr j)` embeds the markings swallowing `L (inr j)` into that powerset.
      rw [hbadR, ← hpow (Sum.inr j)]
      refine card_le_card_of_injOn (fun T => T \ L (Sum.inr j)) ?_ ?_
      · intro T hT
        rw [mem_coe, mem_filter, mem_powerset] at hT
        rw [mem_coe, mem_powerset]
        intro x hx
        rw [mem_sdiff] at hx ⊢
        exact ⟨hT.1 hx.1, hx.2⟩
      · intro T₁ h₁ T₂ h₂ heq
        rw [mem_coe, mem_filter] at h₁ h₂
        simp only at heq
        rw [← sdiff_union_of_subset h₁.2, ← sdiff_union_of_subset h₂.2, heq]
  -- Union bound: the starving markings are outnumbered by the markings.
  have hcard : #(univ.biUnion bad) < #(C.powerset) := by
    have h1 : #(univ.biUnion bad) ≤ ∑ v : Fin n ⊕ Fin n, #(bad v) := card_biUnion_le
    have h2 : ∑ v : Fin n ⊕ Fin n, #(bad v) ≤ (n + n) * 2 ^ (#C - k) := by
      calc ∑ v : Fin n ⊕ Fin n, #(bad v)
          ≤ ∑ _v : Fin n ⊕ Fin n, 2 ^ (#C - k) := sum_le_sum fun v _ => hbadcard v
        _ = (n + n) * 2 ^ (#C - k) := by
            simp [sum_const, card_univ, Fintype.card_sum]
    -- `2 * n < 2 ^ k` is exactly where `hn : n < 2 ^ (k - 1)` is spent.
    have hsplitk : 2 ^ (k - 1) * 2 = 2 ^ k := by
      rw [← pow_succ, Nat.sub_add_cancel hk]
    have hsplitC : 2 ^ k * 2 ^ (#C - k) = 2 ^ #C := by
      rw [← pow_add, Nat.add_sub_cancel' hkC]
    have h3 : (n + n) * 2 ^ (#C - k) < 2 ^ #C := by
      rw [← hsplitC]
      refine (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).2 ?_
      omega
    rw [card_powerset]
    omega
  obtain ⟨T, hTC, hTbad⟩ := exists_mem_notMem_of_card_lt_card hcard
  rw [mem_powerset] at hTC
  have hTbad' : ∀ v, T ∉ bad v := fun v hv => hTbad (mem_biUnion.2 ⟨v, mem_univ v, hv⟩)
  -- Under a marking that starves nobody, the left side keeps a reserved colour and the
  -- right side keeps an unreserved one, so the two sides never collide.
  have hleft : ∀ i : Fin n, ∃ c, c ∈ L (Sum.inl i) ∧ c ∈ T := by
    intro i
    have hi := hTbad' (Sum.inl i)
    rw [hbadL, mem_filter, mem_powerset, not_and] at hi
    obtain ⟨c, hc⟩ := nonempty_iff_ne_empty.2 (hi hTC)
    exact ⟨c, (mem_inter.1 hc).1, (mem_inter.1 hc).2⟩
  have hright : ∀ j : Fin n, ∃ c, c ∈ L (Sum.inr j) ∧ c ∉ T := by
    intro j
    have hj := hTbad' (Sum.inr j)
    rw [hbadR, mem_filter, mem_powerset, not_and] at hj
    exact not_subset.1 (hj hTC)
  refine ⟨Sum.elim (fun i => (hleft i).choose) (fun j => (hright j).choose), ?_, ?_⟩
  · rintro (i | j)
    · exact (hleft i).choose_spec.1
    · exact (hright j).choose_spec.1
  · intro i j hij
    simp only [Sum.elim_inl, Sum.elim_inr] at hij
    exact (hright j).choose_spec.2 (hij ▸ (hleft i).choose_spec.2)

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
