import ProbMethods.Chapter06.ProductLLL

/-!
# §1.1 — Theorem 1.1.9, the Ramsey lower bound from the local lemma

Zhao, *Probabilistic Methods in Combinatorics*, Theorem 1.1.9 (Spencer 1977):

    if e (C(k,2)·C(n,k-2) + 1) · 2^{1-C(k,2)} ≤ 1  then  R(k,k) > n.

This is Theorem 1.1.8 — the local lemma in the random variable model, here
`PMC.exists_avoiding_of_lll` — applied to the uniform random 2-colouring of the edges of
`Kₙ`, with one bad event per `k`-subset.

Three points where the formalization differs from the notes' presentation:

* **the coordinate type is every subset, not every edge.** A colouring is
  `f : Finset (Fin n) → Bool`, and only the 2-element subsets are ever looked at. The extra
  coordinates are independent and no event depends on them, so they cost nothing — and
  `S.powersetCard 2` then gives the edges inside `S` with `Finset.card_powersetCard` handing
  over `#(S.powersetCard 2) = C(#S, 2)` for free.
* **the dependency count needs no canonical choice.** The notes bound the number of `S'` with
  `#(S ∩ S') ≥ 2` by `C(k,2)·C(n,k-2)`: pick the two shared vertices inside `S`, then the
  remaining `k-2` vertices anywhere. Formally `S' ↦ (T, S' \ T)` for *any* 2-subset
  `T ⊆ S ∩ S'` is injective, because `T ⊆ S'` makes `S'` recoverable as `T ∪ (S' \ T)`. So
  the two shared vertices can be chosen arbitrarily, and no ordering of `Fin n` is used.
* **`n < k` is separated off.** The local lemma needs `0 < d`, and `d = C(k,2)·C(n,k-2)`
  vanishes when `n < k - 2`; but then `Kₙ` has no `k`-clique at all and the conclusion is
  immediate. For `2 ≤ k ≤ n` the degree is genuinely positive.
-/

open Finset

namespace PMC

section RamseyLLL

variable {n k : ℕ}

/-- `S` is monochromatic under the edge-colouring `f`: every 2-element subset of `S` gets the
same colour. -/
def MonoOn (S : Finset (Fin n)) (f : Finset (Fin n) → Bool) : Prop :=
  (∀ e ∈ S.powersetCard 2, f e = true) ∨ (∀ e ∈ S.powersetCard 2, f e = false)

instance decidableMonoOn (S : Finset (Fin n)) : DecidablePred (MonoOn S) := fun f => by
  unfold MonoOn
  infer_instance

/-- The bad event attached to a `k`-subset: it is monochromatic. -/
def badMono (S : Finset (Fin n)) : Finset (Finset (Fin n) → Bool) :=
  (univ : Finset (Finset (Fin n) → Bool)).filter fun f => MonoOn S f

@[simp] lemma mem_badMono (S : Finset (Fin n)) (f : Finset (Fin n) → Bool) :
    f ∈ badMono S ↔ MonoOn S f := by
  simp [badMono]

lemma determinedOn_badMono (S : Finset (Fin n)) :
    DeterminedOn (S.powersetCard 2) (badMono S) := by
  intro f g hfg
  rw [mem_badMono, mem_badMono, MonoOn, MonoOn]
  constructor
  · rintro (h | h)
    · exact Or.inl fun e he => by rw [← hfg e he]; exact h e he
    · exact Or.inr fun e he => by rw [← hfg e he]; exact h e he
  · rintro (h | h)
    · exact Or.inl fun e he => by rw [hfg e he]; exact h e he
    · exact Or.inr fun e he => by rw [hfg e he]; exact h e he

/-- The probability that a `k`-subset is monochromatic is `2 · 2^{-C(k,2)}`.

The two colours give two disjoint events, each of probability `(1/2)^{C(k,2)}` by
`PMC.wprob_unifProd_forall`; disjointness needs `S` to span at least one edge. -/
lemma wprob_badMono (S : Finset (Fin n)) (hS : 2 ≤ #S) :
    wprob (unifProd (Finset (Fin n)) Bool) (badMono S)
      = 2 * (1 / 2 : ℝ) ^ (#S).choose 2 := by
  classical
  have hcard : #(S.powersetCard 2) = (#S).choose 2 := Finset.card_powersetCard 2 S
  have hne : (S.powersetCard 2).Nonempty := Finset.powersetCard_nonempty.mpr hS
  -- the two monochromatic events, and their probabilities
  have hgen : ∀ b : Bool,
      wprob (unifProd (Finset (Fin n)) Bool)
        ((univ : Finset (Finset (Fin n) → Bool)).filter
          fun f => ∀ e ∈ S.powersetCard 2, f e = b)
        = (1 / 2 : ℝ) ^ (#S).choose 2 := by
    intro b
    have h := wprob_unifProd_forall (β := Bool) (S.powersetCard 2) (fun _ c => c = b)
    rw [h, Finset.prod_congr rfl fun e _ => ?_, Finset.prod_const, hcard]
    have : #((univ : Finset Bool).filter fun c => c = b) = 1 := by
      rw [Finset.filter_eq' univ b]
      simp
    rw [this]
    norm_num
  set U : Finset (Finset (Fin n) → Bool) :=
    (univ : Finset (Finset (Fin n) → Bool)).filter
      fun f => ∀ e ∈ S.powersetCard 2, f e = true with hU
  set V : Finset (Finset (Fin n) → Bool) :=
    (univ : Finset (Finset (Fin n) → Bool)).filter
      fun f => ∀ e ∈ S.powersetCard 2, f e = false with hV
  have hmemU : ∀ f, f ∈ U ↔ ∀ e ∈ S.powersetCard 2, f e = true := by
    intro f; rw [hU]; simp
  have hmemV : ∀ f, f ∈ V ↔ ∀ e ∈ S.powersetCard 2, f e = false := by
    intro f; rw [hV]; simp
  have hdisj : Disjoint U V := by
    refine Finset.disjoint_left.mpr fun f hf hf' => ?_
    obtain ⟨e, he⟩ := hne
    have h1 := (hmemU f).mp hf e he
    have h2 := (hmemV f).mp hf' e he
    rw [h1] at h2
    exact Bool.noConfusion h2
  have hsplit : badMono S = U ∪ V := by
    ext f
    rw [mem_badMono, Finset.mem_union, hmemU, hmemV, MonoOn]
  have hadd : wprob (unifProd (Finset (Fin n)) Bool) (U ∪ V)
      = wprob (unifProd (Finset (Fin n)) Bool) U
        + wprob (unifProd (Finset (Fin n)) Bool) V := by
    simp only [wprob]
    exact Finset.sum_union hdisj
  rw [hsplit, hadd, hU, hV, hgen true, hgen false]
  ring

/-- The `k`-subsets other than `S` that share at least two vertices with it — exactly those
whose edge sets meet `S`'s. -/
def nearby (k : ℕ) (S : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  ((univ : Finset (Fin n)).powersetCard k).filter fun S' => S' ≠ S ∧ 2 ≤ #(S ∩ S')

/-- **The dependency count.** At most `C(k,2)·C(n,k-2)` of the `k`-subsets share two vertices
with a given one: `S' ↦ (T, S' \ T)` for any 2-subset `T ⊆ S ∩ S'` is injective, since
`T ⊆ S'` makes `S'` recoverable. No canonical choice of `T` is needed. -/
lemma card_nearby_le (S : Finset (Fin n)) (hS : #S = k) :
    #(nearby k S) ≤ k.choose 2 * n.choose (k - 2) := by
  classical
  -- choose two shared vertices for each nearby set
  have hex : ∀ S' : Finset (Fin n), ∃ T : Finset (Fin n),
      S' ∈ nearby k S → (T ⊆ S ∩ S' ∧ #T = 2) := by
    intro S'
    by_cases h : S' ∈ nearby k S
    · have h2 : 2 ≤ #(S ∩ S') := by
        rw [nearby, mem_filter] at h
        exact h.2.2
      obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq h2
      exact ⟨T, fun _ => ⟨hTsub, hTcard⟩⟩
    · exact ⟨∅, fun h' => absurd h' h⟩
  choose T hT using hex
  have hmaps : ∀ S' ∈ nearby k S,
      (T S', S' \ T S') ∈ (S.powersetCard 2) ×ˢ ((univ : Finset (Fin n)).powersetCard (k - 2)) := by
    intro S' hS'
    obtain ⟨hTsub, hTcard⟩ := hT S' hS'
    have hTS : T S' ⊆ S := hTsub.trans Finset.inter_subset_left
    have hTS' : T S' ⊆ S' := hTsub.trans Finset.inter_subset_right
    have hS'card : #S' = k := by
      rw [nearby, mem_filter, Finset.mem_powersetCard] at hS'
      exact hS'.1.2
    rw [Finset.mem_product, Finset.mem_powersetCard, Finset.mem_powersetCard]
    refine ⟨⟨hTS, hTcard⟩, Finset.subset_univ _, ?_⟩
    rw [Finset.card_sdiff_of_subset hTS', hTcard, hS'card]
  have hinj : Set.InjOn (fun S' => (T S', S' \ T S')) (nearby k S) := by
    intro S₁ h₁ S₂ h₂ heq
    have e1 : T S₁ = T S₂ := (Prod.mk.injEq .. ▸ heq).1
    have e2 : S₁ \ T S₁ = S₂ \ T S₂ := (Prod.mk.injEq .. ▸ heq).2
    have hs1 : T S₁ ∪ (S₁ \ T S₁) = S₁ :=
      Finset.union_sdiff_of_subset ((hT S₁ h₁).1.trans Finset.inter_subset_right)
    have hs2 : T S₂ ∪ (S₂ \ T S₂) = S₂ :=
      Finset.union_sdiff_of_subset ((hT S₂ h₂).1.trans Finset.inter_subset_right)
    rw [← hs1, e2, e1, hs2]
  calc #(nearby k S)
      ≤ #((S.powersetCard 2) ×ˢ ((univ : Finset (Fin n)).powersetCard (k - 2))) :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ = k.choose 2 * n.choose (k - 2) := by
        rw [Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard, hS,
          card_univ, Fintype.card_fin]

/-- **Theorem 1.1.9 (Spencer 1977).** If

    e · (C(k,2)·C(n,k-2) + 1) · 2^{1-C(k,2)} ≤ 1

then `R(k,k) > n`. (`2 · (1/2)^{C(k,2)}` below is `2^{1-C(k,2)}`, written without a negative
exponent; the notes' hypothesis is the strict inequality, so this is the weaker one.)

The local lemma is `PMC.exists_avoiding_of_lll` — Theorem 1.1.8 — with one bad event per
`k`-subset, each depending on the `C(k,2)` coordinates indexing its edges. -/
theorem not_ramseyProp_of_lll (hk : 2 ≤ k)
    (hep : Real.exp 1 * (2 * (1 / 2 : ℝ) ^ k.choose 2)
        * ((k.choose 2 * n.choose (k - 2) : ℝ) + 1) ≤ 1) :
    ¬ RamseyProp n k k := by
  classical
  rcases lt_or_ge n k with hnk | hnk
  · -- no `k`-clique exists at all
    rw [not_ramseyProp_iff]
    refine ⟨⊥, ?_, ?_⟩ <;>
      exact SimpleGraph.cliqueFree_of_card_lt (by simpa using hnk)
  -- the local lemma on the uniform random colouring
  set κ := {S : Finset (Fin n) // #S = k} with hκ
  have hdpos : 0 < k.choose 2 * n.choose (k - 2) := by
    refine Nat.mul_pos (Nat.choose_pos hk) (Nat.choose_pos ?_)
    omega
  have hprob : ∀ c : κ, wprob (unifProd (Finset (Fin n)) Bool) (badMono c.1)
      ≤ 2 * (1 / 2 : ℝ) ^ k.choose 2 := by
    intro c
    rw [wprob_badMono c.1 (by rw [c.2]; exact hk), c.2]
  obtain ⟨f, hf⟩ := exists_avoiding_of_lll (ι := Finset (Fin n)) (β := Bool) (κ := κ)
    (fun c => badMono c.1) (fun c => c.1.powersetCard 2)
    (fun c => determinedOn_badMono c.1)
    (fun c => (univ : Finset κ).filter fun c' => c'.1 ∈ nearby k c.1)
    hdpos (by positivity)
    (by
      intro c hc
      rw [mem_filter, nearby, mem_filter] at hc
      exact hc.2.2.1 rfl)
    (by
      intro c
      refine le_trans (Finset.card_le_card_of_injOn Subtype.val ?_ (fun a _ b _ h => Subtype.ext h))
        (card_nearby_le c.1 c.2)
      intro c' hc'
      simp only [Finset.mem_coe, mem_filter] at hc'
      exact hc'.2)
    (by
      intro c c' hc'
      -- `c'` is neither `c` nor nearby, so the two vertex sets share at most one vertex
      have hne : c' ≠ c := fun h => hc' (by rw [h]; exact Finset.mem_insert_self _ _)
      have hnot : c'.1 ∉ nearby k c.1 := by
        intro hmem
        exact hc' (Finset.mem_insert_of_mem (mem_filter.mpr ⟨mem_univ _, hmem⟩))
      have hcne : c'.1 ≠ c.1 := fun h => hne (Subtype.ext h)
      have hcap : #(c.1 ∩ c'.1) ≤ 1 := by
        by_contra hcon
        rw [nearby, mem_filter, Finset.mem_powersetCard] at hnot
        exact hnot ⟨⟨Finset.subset_univ _, c'.2⟩, fun h => hne (Subtype.ext h), by omega⟩
      refine Finset.disjoint_left.mpr fun e he he' => ?_
      rw [Finset.mem_powersetCard] at he he'
      have hsub : e ⊆ c.1 ∩ c'.1 := Finset.subset_inter he.1 he'.1
      have : 2 ≤ #(c.1 ∩ c'.1) := he.2 ▸ Finset.card_le_card hsub
      omega)
    hprob (by push_cast; exact hep)
  -- read the colouring as a graph
  set G : SimpleGraph (Fin n) :=
    { Adj := fun u v => u ≠ v ∧ f {u, v} = true
      symm := ⟨fun u v h => ⟨h.1.symm, by rw [Finset.pair_comm]; exact h.2⟩⟩
      loopless := ⟨fun u h => h.1 rfl⟩ } with hG
  have hGadj : ∀ u v, G.Adj u v ↔ (u ≠ v ∧ f {u, v} = true) := fun _ _ => Iff.rfl
  rw [not_ramseyProp_iff]
  refine ⟨G, ?_, ?_⟩
  · -- a red `k`-clique would be monochromatic in `true`
    intro s hs
    have hcard : #s = k := hs.2
    refine hf ⟨s, hcard⟩ ?_
    rw [mem_badMono]
    refine Or.inl fun e he => ?_
    rw [Finset.mem_powersetCard] at he
    obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp he.2
    have hu : u ∈ s := he.1 (by simp)
    have hv : v ∈ s := he.1 (by simp)
    exact ((hGadj u v).mp (hs.1 hu hv huv)).2
  · -- a blue `k`-clique would be monochromatic in `false`
    intro s hs
    have hcard : #s = k := hs.2
    refine hf ⟨s, hcard⟩ ?_
    rw [mem_badMono]
    refine Or.inr fun e he => ?_
    rw [Finset.mem_powersetCard] at he
    obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp he.2
    have hu : u ∈ s := he.1 (by simp)
    have hv : v ∈ s := he.1 (by simp)
    have hcompl := hs.1 hu hv huv
    rw [SimpleGraph.compl_adj] at hcompl
    have := hcompl.2
    rw [hGadj] at this
    rcases Bool.eq_false_or_eq_true (f {u, v}) with h | h
    · exact absurd ⟨huv, h⟩ this
    · exact h

end RamseyLLL


end PMC
