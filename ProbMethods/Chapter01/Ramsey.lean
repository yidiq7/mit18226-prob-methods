import ProbMethods.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset

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
  sorry

end PMC
