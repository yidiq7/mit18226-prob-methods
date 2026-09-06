import ProbMethods.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Sym.Card

/-!
# §1.1 — Lower bounds to Ramsey numbers

Zhao, *Probabilistic Methods in Combinatorics*, Theorems 1.1.2 and 1.1.6.
-/

open Finset

namespace PMC

section ErdosCounting

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- The colourings of `β` that are constantly `b` on `T` are exactly the colourings of the
complement of `T`, extended by `b`. -/
private def constOnEquiv (T : Finset β) (b : Bool) :
    {f : β → Bool // ∀ x ∈ T, f x = b} ≃ ({x : β // x ∉ T} → Bool) where
  toFun f x := f.1 x.1
  invFun v := ⟨fun x => if h : x ∈ T then b else v ⟨x, h⟩, fun x hx => by simp [hx]⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ T
    · simp [hx, f.2 x hx]
    · simp [hx]
  right_inv v := by
    funext x
    simp [x.2]

/-- One colouring in `2 ^ #T` is constantly `b` on `T`. Stated multiplicatively to keep the
exponent free of truncated subtraction. -/
private lemma card_filter_const_mul (T : Finset β) (b : Bool) :
    #(univ.filter fun f : β → Bool => ∀ x ∈ T, f x = b) * 2 ^ #T = 2 ^ Fintype.card β := by
  have hcard : #(univ.filter fun f : β → Bool => ∀ x ∈ T, f x = b)
      = 2 ^ (Fintype.card β - #T) := by
    rw [← Fintype.card_subtype, Fintype.card_congr (constOnEquiv T b), Fintype.card_fun,
      Fintype.card_bool, Fintype.card_subtype_compl, Fintype.card_coe]
  rw [hcard, ← pow_add, Nat.sub_add_cancel (by simpa using Finset.card_le_univ T)]

end ErdosCounting

section ErdosGraphs

variable {n : ℕ}

/-- The graph on `Fin n` whose edges are the pairs `{a, b}` with `f {a, b} = true`. As `f`
ranges over all `2 ^ C(n,2)` relevant colourings, `graphOf f` ranges over every red/blue
colouring of `Kₙ`, red being adjacency. -/
private def graphOf (f : Finset (Fin n) → Bool) : SimpleGraph (Fin n) where
  Adj a b := a ≠ b ∧ f {a, b}
  symm := ⟨fun a b h => ⟨h.1.symm, by rw [Finset.pair_comm]; exact h.2⟩⟩
  loopless := ⟨fun a h => h.1 rfl⟩

/-- The colourings for which the `k`-set `t` is monochromatic of colour `b`: a red `K_k`
when `b = true`, a blue one when `b = false`. -/
private def badSet (t : Finset (Fin n)) (b : Bool) : Finset (Finset (Fin n) → Bool) :=
  univ.filter fun f => ∀ e ∈ powersetCard 2 t, f e = b

private lemma mem_badSet {f : Finset (Fin n) → Bool} {t : Finset (Fin n)} {b : Bool}
    (ht : ∀ a ∈ t, ∀ c ∈ t, a ≠ c → f {a, c} = b) : f ∈ badSet t b := by
  simp only [badSet, mem_filter, mem_univ, true_and]
  intro e he
  rw [mem_powersetCard] at he
  obtain ⟨a, c, hac, rfl⟩ := Finset.card_eq_two.mp he.2
  exact ht a (he.1 (by simp)) c (he.1 (by simp)) hac

/-- `#(badSet t b)` is a `2 ^ C(k,2)` fraction of all colourings, for `t` of size `k`. -/
private lemma card_badSet_mul {t : Finset (Fin n)} {k : ℕ} (hk : #t = k) (b : Bool) :
    #(badSet t b) * 2 ^ k.choose 2 = 2 ^ Fintype.card (Finset (Fin n)) := by
  have hT : #(powersetCard 2 t) = k.choose 2 := by rw [Finset.card_powersetCard, hk]
  rw [badSet, ← hT]
  exact card_filter_const_mul _ _

end ErdosGraphs
/-- **Erdős' Ramsey lower bound** (Zhao, Theorem 1.1.2; Erdős 1947).

If `(n.choose k) * 2 ^ (1 - k.choose 2) < 1` then `R(k, k) > n`.

The hypothesis is stated without real exponents by clearing denominators: for `k ≥ 2`,
`(n.choose k) * 2 ^ (1 - k.choose 2) < 1` is equivalent to `2 * n.choose k < 2 ^ k.choose 2`.

The book's proof colours the edges of `Kₙ` red/blue independently and uniformly. Each of
the `n.choose k` vertex `k`-sets induces a monochromatic `K_k` with probability
`2 ^ (1 - k.choose 2)`, so by the union bound the probability that some `k`-set is
monochromatic is less than `1`; hence some colouring has none. -/
theorem not_ramseyProp_of_two_mul_choose_lt {n k : ℕ}
    (h : 2 * n.choose k < 2 ^ k.choose 2) : ¬ RamseyProp n k k := by
  intro hR
  set idx := (powersetCard k (univ : Finset (Fin n))) ×ˢ (univ : Finset Bool) with hidx
  -- Every colouring is bad: some `k`-set is monochromatic in one colour or the other.
  have hcover : (univ : Finset (Finset (Fin n) → Bool)) ⊆
      idx.biUnion fun p => badSet p.1 p.2 := by
    intro f _
    rw [mem_biUnion]
    rcases hR (graphOf f) with hne | hne <;>
      simp only [SimpleGraph.CliqueFree, not_forall, not_not] at hne <;>
      obtain ⟨t, ht⟩ := hne <;> rw [SimpleGraph.isNClique_iff] at ht
    · refine ⟨(t, true), by simp [hidx, mem_product, ht.2], mem_badSet ?_⟩
      intro a ha c hc hac
      exact (ht.1 (mem_coe.mpr ha) (mem_coe.mpr hc) hac).2
    · refine ⟨(t, false), by simp [hidx, mem_product, ht.2], mem_badSet ?_⟩
      intro a ha c hc hac
      have := (ht.1 (mem_coe.mpr ha) (mem_coe.mpr hc) hac)
      rw [SimpleGraph.compl_adj] at this
      simpa [graphOf, hac] using this.2
  -- Counting: the bad colourings are too few to cover everything.
  have hsum : (2 : ℕ) ^ Fintype.card (Finset (Fin n)) ≤ ∑ p ∈ idx, #(badSet p.1 p.2) :=
    calc (2 : ℕ) ^ Fintype.card (Finset (Fin n))
        = #(univ : Finset (Finset (Fin n) → Bool)) := by
          rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool]
      _ ≤ #(idx.biUnion fun p => badSet p.1 p.2) := Finset.card_le_card hcover
      _ ≤ ∑ p ∈ idx, #(badSet p.1 p.2) := Finset.card_biUnion_le
  have hmul : (∑ p ∈ idx, #(badSet p.1 p.2)) * 2 ^ k.choose 2
      = n.choose k * 2 * 2 ^ Fintype.card (Finset (Fin n)) := by
    rw [Finset.sum_mul, Finset.sum_congr rfl (fun p hp => ?_), Finset.sum_const, smul_eq_mul,
      hidx, Finset.card_product, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
      Finset.card_univ, Fintype.card_bool]
    rw [hidx, mem_product, mem_powersetCard] at hp
    exact card_badSet_mul hp.1.2 p.2
  have hpos : 0 < (2 : ℕ) ^ Fintype.card (Finset (Fin n)) := pow_pos (by norm_num) _
  have h1 : 2 ^ Fintype.card (Finset (Fin n)) * 2 ^ k.choose 2
      ≤ n.choose k * 2 * 2 ^ Fintype.card (Finset (Fin n)) := by
    rw [← hmul]; exact Nat.mul_le_mul_right _ hsum
  have h2 : n.choose k * 2 * 2 ^ Fintype.card (Finset (Fin n))
      < 2 ^ k.choose 2 * 2 ^ Fintype.card (Finset (Fin n)) :=
    (Nat.mul_lt_mul_right hpos).mpr (by omega)
  have h3 : 2 ^ Fintype.card (Finset (Fin n)) * 2 ^ k.choose 2
      < 2 ^ k.choose 2 * 2 ^ Fintype.card (Finset (Fin n)) := h1.trans_lt h2
  rw [mul_comm (2 ^ Fintype.card (Finset (Fin n))) (2 ^ k.choose 2)] at h3
  exact Nat.lt_irrefl _ h3

section Alteration

variable {n : ℕ}

/-- The edges spanned by a vertex set `t`, as elements of `Sym2 (Fin n)`. There are
`C(#t, 2)` of them. -/
private def edgesOn (t : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  t.offDiag.image Sym2.mk.uncurry

private lemma card_edgesOn (t : Finset (Fin n)) : #(edgesOn t) = (#t).choose 2 :=
  Sym2.card_image_offDiag t

private lemma exists_of_mem_edgesOn {t : Finset (Fin n)} {x : Sym2 (Fin n)}
    (hx : x ∈ edgesOn t) : ∃ a ∈ t, ∃ b ∈ t, a ≠ b ∧ x = s(a, b) := by
  obtain ⟨⟨a, b⟩, hp, rfl⟩ := mem_image.1 hx
  obtain ⟨ha, hb, hab⟩ := mem_offDiag.1 hp
  exact ⟨a, ha, b, hb, hab, rfl⟩

/-- A colouring of the edges of `Kₙ` is a set `A` of red edges. The `k`-sets that are
monochromatic under `A`: either every edge they span is red, or none is. -/
private def monoSets (k : ℕ) (A : Finset (Sym2 (Fin n))) : Finset (Finset (Fin n)) :=
  {t ∈ powersetCard k (univ : Finset (Fin n)) | edgesOn t ⊆ A ∨ edgesOn t ∩ A = ∅}

private lemma monoSets_def (k : ℕ) (A : Finset (Sym2 (Fin n))) :
    monoSets k A =
      {t ∈ powersetCard k (univ : Finset (Fin n)) | edgesOn t ⊆ A ∨ edgesOn t ∩ A = ∅} :=
  rfl

private lemma mem_monoSets {k : ℕ} {A : Finset (Sym2 (Fin n))} {t : Finset (Fin n)} :
    t ∈ monoSets k A ↔ #t = k ∧ (edgesOn t ⊆ A ∨ edgesOn t ∩ A = ∅) := by
  rw [monoSets_def, mem_filter, mem_powersetCard]
  exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨subset_univ t, h.1⟩, h.2⟩⟩

/-- At most `2 ^ (#α - #D)` of the subsets of `α` contain `D`. -/
private lemma card_powerset_filter_superset_le {α : Type*} [Fintype α] [DecidableEq α]
    (D : Finset α) :
    #{A ∈ (univ : Finset α).powerset | D ⊆ A} ≤ 2 ^ (Fintype.card α - #D) := by
  have hc : #(((univ : Finset α) \ D).powerset) = 2 ^ (Fintype.card α - #D) := by
    rw [card_powerset, card_sdiff_of_subset (subset_univ D), card_univ]
  rw [← hc]
  refine card_le_card_of_injOn (fun A => A \ D) ?_ ?_
  · intro A _
    rw [mem_coe, mem_powerset]
    intro x hx
    exact mem_sdiff.2 ⟨mem_univ x, (mem_sdiff.1 hx).2⟩
  · intro A₁ h₁ A₂ h₂ heq
    rw [mem_coe, mem_filter] at h₁ h₂
    simp only at heq
    rw [← sdiff_union_of_subset h₁.2, ← sdiff_union_of_subset h₂.2, heq]

/-- At most `2 ^ (#α - #D)` of the subsets of `α` are disjoint from `D`. -/
private lemma card_powerset_filter_inter_le {α : Type*} [Fintype α] [DecidableEq α]
    (D : Finset α) :
    #{A ∈ (univ : Finset α).powerset | D ∩ A = ∅} ≤ 2 ^ (Fintype.card α - #D) := by
  have hc : #(((univ : Finset α) \ D).powerset) = 2 ^ (Fintype.card α - #D) := by
    rw [card_powerset, card_sdiff_of_subset (subset_univ D), card_univ]
  rw [← hc]
  refine card_le_card fun A hA => ?_
  rw [mem_filter] at hA
  rw [mem_powerset]
  intro x hx
  refine mem_sdiff.2 ⟨mem_univ x, fun hxD => ?_⟩
  have hmem : x ∈ D ∩ A := mem_inter.2 ⟨hxD, hx⟩
  rw [hA.2] at hmem
  exact notMem_empty x hmem

/-- **The averaging step.** Some colouring of `Kₙ` has at most `C(n,k) / 2 ^ (C(k,2) - 1)`
monochromatic `k`-sets, because that is the mean over all `2 ^ M` colourings: each of the
`C(n,k)` vertex `k`-sets is monochromatic under at most `2 * 2 ^ (M - C(k,2))` of them. -/
private lemma exists_colouring_monoSets_le (n k : ℕ) (hk : 2 ≤ k) :
    ∃ A : Finset (Sym2 (Fin n)), #(monoSets k A) * 2 ^ (k.choose 2 - 1) ≤ n.choose k := by
  rcases Nat.lt_or_ge n k with hkn | hkn
  · -- `Fin n` has no `k`-subsets at all.
    refine ⟨∅, ?_⟩
    have hempty : powersetCard k (univ : Finset (Fin n)) = ∅ := by
      rw [powersetCard_eq_empty, card_univ, Fintype.card_fin]
      exact hkn
    rw [monoSets_def, hempty]
    simp
  have hK1 : 1 ≤ k.choose 2 := Nat.choose_pos hk
  have hKM : k.choose 2 ≤ Fintype.card (Sym2 (Fin n)) := by
    obtain ⟨t, ht⟩ : (powersetCard k (univ : Finset (Fin n))).Nonempty := by
      rw [powersetCard_nonempty, card_univ, Fintype.card_fin]
      exact hkn
    rw [mem_powersetCard] at ht
    calc k.choose 2 = #(edgesOn t) := by rw [card_edgesOn, ht.2]
      _ ≤ Fintype.card (Sym2 (Fin n)) := by
          rw [← card_univ]; exact card_le_card (subset_univ _)
  obtain ⟨A, hAmem, hAmin⟩ := exists_min_image ((univ : Finset (Sym2 (Fin n))).powerset)
    (fun A => #(monoSets k A)) ⟨∅, by simp⟩
  refine ⟨A, ?_⟩
  -- Double count pairs (colouring, monochromatic `k`-set).
  have hsum : ∑ B ∈ (univ : Finset (Sym2 (Fin n))).powerset, #(monoSets k B)
      ≤ n.choose k * (2 * 2 ^ (Fintype.card (Sym2 (Fin n)) - k.choose 2)) := by
    calc ∑ B ∈ (univ : Finset (Sym2 (Fin n))).powerset, #(monoSets k B)
        = ∑ B ∈ (univ : Finset (Sym2 (Fin n))).powerset,
            ∑ t ∈ powersetCard k (univ : Finset (Fin n)),
              (if edgesOn t ⊆ B ∨ edgesOn t ∩ B = ∅ then 1 else 0) :=
          sum_congr rfl fun B _ => by rw [monoSets_def, card_filter]
      _ = ∑ t ∈ powersetCard k (univ : Finset (Fin n)),
            ∑ B ∈ (univ : Finset (Sym2 (Fin n))).powerset,
              (if edgesOn t ⊆ B ∨ edgesOn t ∩ B = ∅ then 1 else 0) := sum_comm
      _ ≤ ∑ _t ∈ powersetCard k (univ : Finset (Fin n)),
            2 * 2 ^ (Fintype.card (Sym2 (Fin n)) - k.choose 2) := by
          refine sum_le_sum fun t ht => ?_
          rw [← card_filter]
          rw [mem_powersetCard] at ht
          have hEt : #(edgesOn t) = k.choose 2 := by rw [card_edgesOn, ht.2]
          calc #{B ∈ (univ : Finset (Sym2 (Fin n))).powerset |
                    edgesOn t ⊆ B ∨ edgesOn t ∩ B = ∅}
              ≤ #{B ∈ (univ : Finset (Sym2 (Fin n))).powerset | edgesOn t ⊆ B}
                  + #{B ∈ (univ : Finset (Sym2 (Fin n))).powerset | edgesOn t ∩ B = ∅} := by
                rw [filter_or]; exact card_union_le _ _
            _ ≤ 2 ^ (Fintype.card (Sym2 (Fin n)) - k.choose 2)
                  + 2 ^ (Fintype.card (Sym2 (Fin n)) - k.choose 2) := by
                refine Nat.add_le_add ?_ ?_
                · rw [← hEt]; exact card_powerset_filter_superset_le _
                · rw [← hEt]; exact card_powerset_filter_inter_le _
            _ = 2 * 2 ^ (Fintype.card (Sym2 (Fin n)) - k.choose 2) := (two_mul _).symm
      _ = n.choose k * (2 * 2 ^ (Fintype.card (Sym2 (Fin n)) - k.choose 2)) := by
          rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, smul_eq_mul]
  have hmin : 2 ^ Fintype.card (Sym2 (Fin n)) * #(monoSets k A)
      ≤ ∑ B ∈ (univ : Finset (Sym2 (Fin n))).powerset, #(monoSets k B) := by
    have h := card_nsmul_le_sum ((univ : Finset (Sym2 (Fin n))).powerset)
      (fun B => #(monoSets k B)) (#(monoSets k A)) fun B hB => hAmin B hB
    rwa [card_powerset, card_univ, smul_eq_mul] at h
  have hpowid : 2 * 2 ^ (Fintype.card (Sym2 (Fin n)) - k.choose 2) * 2 ^ (k.choose 2 - 1)
      = 2 ^ Fintype.card (Sym2 (Fin n)) := by
    have e1 : Fintype.card (Sym2 (Fin n)) - k.choose 2 + (k.choose 2 - 1) + 1
        = Fintype.card (Sym2 (Fin n)) := by omega
    rw [mul_comm 2 (2 ^ (Fintype.card (Sym2 (Fin n)) - k.choose 2)), mul_right_comm,
      ← pow_add, ← pow_succ, e1]
  refine Nat.le_of_mul_le_mul_left ?_ (Nat.two_pow_pos (Fintype.card (Sym2 (Fin n))))
  calc 2 ^ Fintype.card (Sym2 (Fin n)) * (#(monoSets k A) * 2 ^ (k.choose 2 - 1))
      = 2 ^ Fintype.card (Sym2 (Fin n)) * #(monoSets k A) * 2 ^ (k.choose 2 - 1) :=
        (mul_assoc _ _ _).symm
    _ ≤ n.choose k * (2 * 2 ^ (Fintype.card (Sym2 (Fin n)) - k.choose 2))
          * 2 ^ (k.choose 2 - 1) := Nat.mul_le_mul (hmin.trans hsum) (le_refl _)
    _ = n.choose k * (2 * 2 ^ (Fintype.card (Sym2 (Fin n)) - k.choose 2)
          * 2 ^ (k.choose 2 - 1)) := mul_assoc _ _ _
    _ = n.choose k * 2 ^ Fintype.card (Sym2 (Fin n)) := by rw [hpowid]
    _ = 2 ^ Fintype.card (Sym2 (Fin n)) * n.choose k := mul_comm _ _

/-- The graph on `Fin m` induced by the colouring `A` along the vertex enumeration `e`:
`a` and `b` are adjacent when the edge `e a e b` is red. -/
private def restrictGraph {m : ℕ} (A : Finset (Sym2 (Fin n))) (e : Fin m → Fin n) :
    SimpleGraph (Fin m) where
  Adj a b := a ≠ b ∧ s(e a, e b) ∈ A
  symm := ⟨fun _ _ h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

end Alteration

/-- **Ramsey lower bound via alteration** (Zhao, Theorem 1.1.6).

For all `k, n` we have `R(k, k) > n - (n.choose k) * 2 ^ (1 - k.choose 2)`.

Stated as: there is an `m` at least that large carrying a red/blue colouring of `K_m` with
no monochromatic `K_k`. For `k ≥ 2` the deleted quantity
`(n.choose k) * 2 ^ (1 - k.choose 2)` equals `(n.choose k) / 2 ^ (k.choose 2 - 1)`.

The book's proof colours `Kₙ` at random, then deletes one vertex from every monochromatic
`K_k`. The expected number of monochromatic `K_k`'s is `(n.choose k) * 2 ^ (1 - k.choose 2)`,
so with positive probability at least that many vertices survive. -/
theorem exists_cliqueFree_of_alteration (n k : ℕ) (hk : 2 ≤ k) :
    ∃ m : ℕ, (n : ℝ) - (n.choose k : ℝ) / 2 ^ (k.choose 2 - 1) ≤ m ∧
      ∃ G : SimpleGraph (Fin m), G.CliqueFree k ∧ Gᶜ.CliqueFree k := by
  obtain ⟨A, hA⟩ := exists_colouring_monoSets_le n k hk
  -- Delete one vertex from every monochromatic `k`-set.
  obtain ⟨D, hDcard, hDmeets⟩ :
      ∃ D : Finset (Fin n), #D ≤ #(monoSets k A) ∧ ∀ t ∈ monoSets k A, ∃ x ∈ t, x ∈ D := by
    refine ⟨(monoSets k A).biUnion fun t => if h : t.Nonempty then {h.choose} else ∅, ?_, ?_⟩
    · refine card_biUnion_le.trans ?_
      calc ∑ t ∈ monoSets k A,
              #(if h : t.Nonempty then ({h.choose} : Finset (Fin n)) else ∅)
          ≤ ∑ _t ∈ monoSets k A, 1 := by
            refine sum_le_sum fun t _ => ?_
            by_cases h : t.Nonempty <;> simp [h]
        _ = #(monoSets k A) := by simp
    · intro t ht
      have hne : t.Nonempty := by
        rw [← card_pos, (mem_monoSets.1 ht).1]
        omega
      refine ⟨hne.choose, hne.choose_spec, mem_biUnion.2 ⟨t, ht, ?_⟩⟩
      rw [dif_pos hne]
      exact mem_singleton_self _
  have hDn : #D ≤ n := by
    have h := card_le_card (subset_univ D)
    rwa [card_univ, Fintype.card_fin] at h
  have hScard : #((univ : Finset (Fin n)) \ D) = n - #D := by
    rw [card_sdiff_of_subset (subset_univ D), card_univ, Fintype.card_fin]
  -- Enumerate what is left after the deletion.
  obtain ⟨e, he_inj, he_mem⟩ :
      ∃ e : Fin #((univ : Finset (Fin n)) \ D) → Fin n,
        Function.Injective e ∧ ∀ i, e i ∈ (univ : Finset (Fin n)) \ D := by
    have φ : Fin #((univ : Finset (Fin n)) \ D) ≃ {x // x ∈ (univ : Finset (Fin n)) \ D} :=
      (Finset.equivFinOfCardEq rfl).symm
    exact ⟨fun i => (φ i : Fin n), fun a b hab => φ.injective (Subtype.ext hab),
      fun i => (φ i).2⟩
  -- Nothing monochromatic survives, because each such set lost a vertex.
  have hkill : ∀ t : Finset (Fin n), (∀ x ∈ t, x ∈ (univ : Finset (Fin n)) \ D) →
      t ∈ monoSets k A → False := by
    intro t hts ht
    obtain ⟨x, hxt, hxD⟩ := hDmeets t ht
    exact (mem_sdiff.1 (hts x hxt)).2 hxD
  have himg : ∀ s' : Finset (Fin #((univ : Finset (Fin n)) \ D)),
      ∀ x ∈ s'.image e, x ∈ (univ : Finset (Fin n)) \ D := by
    intro s' x hx
    obtain ⟨i, _, rfl⟩ := mem_image.1 hx
    exact he_mem i
  refine ⟨#((univ : Finset (Fin n)) \ D), ?_, restrictGraph A e, ?_, ?_⟩
  · -- The deletion costs at most `C(n,k) / 2 ^ (C(k,2) - 1)` vertices.
    have hnat : #D * 2 ^ (k.choose 2 - 1) ≤ n.choose k :=
      le_trans (Nat.mul_le_mul hDcard (le_refl _)) hA
    have hpos : (0 : ℝ) < 2 ^ (k.choose 2 - 1) := by
      exact_mod_cast Nat.two_pow_pos (k.choose 2 - 1)
    have hreal : (#D : ℝ) ≤ (n.choose k : ℝ) / 2 ^ (k.choose 2 - 1) := by
      rw [le_div_iff₀ hpos]
      exact_mod_cast hnat
    have hcast : ((#((univ : Finset (Fin n)) \ D) : ℕ) : ℝ) = (n : ℝ) - (#D : ℝ) := by
      rw [hScard, Nat.cast_sub hDn]
    rw [hcast]
    exact sub_le_sub_left hreal _
  · -- A red `K_k` would be an all-red `k`-set surviving the deletion.
    intro s' hs'
    refine hkill (s'.image e) (himg s') (mem_monoSets.2 ⟨?_, Or.inl ?_⟩)
    · rw [card_image_of_injective _ he_inj, hs'.card_eq]
    · intro x hx
      obtain ⟨u, hu, v, hv, huv, rfl⟩ := exists_of_mem_edgesOn hx
      obtain ⟨a, ha, rfl⟩ := mem_image.1 hu
      obtain ⟨b, hb, rfl⟩ := mem_image.1 hv
      have hab : a ≠ b := fun h => huv (by rw [h])
      exact (hs'.isClique (mem_coe.2 ha) (mem_coe.2 hb) hab).2
  · -- A blue `K_k` would be an all-blue `k`-set surviving the deletion.
    intro s' hs'
    refine hkill (s'.image e) (himg s') (mem_monoSets.2 ⟨?_, Or.inr ?_⟩)
    · rw [card_image_of_injective _ he_inj, hs'.card_eq]
    · rw [← not_nonempty_iff_eq_empty]
      rintro ⟨x, hx⟩
      rw [mem_inter] at hx
      obtain ⟨u, hu, v, hv, huv, rfl⟩ := exists_of_mem_edgesOn hx.1
      obtain ⟨a, ha, rfl⟩ := mem_image.1 hu
      obtain ⟨b, hb, rfl⟩ := mem_image.1 hv
      have hab : a ≠ b := fun h => huv (by rw [h])
      exact (hs'.isClique (mem_coe.2 ha) (mem_coe.2 hb) hab).2 ⟨hab, hx.2⟩

end PMC
