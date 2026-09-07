import ProbMethods.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# §2.1 — Hamiltonian paths in tournaments

Zhao, *Probabilistic Methods in Combinatorics*, Theorem 2.1.2.

The minimisation half of Question 2.1.1 — that the transitive tournament has exactly one
Hamilton path, and that every tournament has at least one — is not a node here; the notes
leave it as an exercise, and it is not a probabilistic argument.
-/

open Finset

namespace PMC

section Szele

variable {n : ℕ}

/-- Functions agreeing with a prescribed `g` on `D` are the functions on `D`'s complement. -/
private def agreeEquiv {α : Type*} [DecidableEq α] (D : Finset α) (g : α → Bool) :
    {f : α → Bool // ∀ x ∈ D, f x = g x} ≃ ({x : α // x ∉ D} → Bool) where
  toFun f x := f.1 x.1
  invFun v := ⟨fun x => if h : x ∈ D then g x else v ⟨x, h⟩, fun x hx => by simp [hx]⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ D
    · simp [hx, f.2 x hx]
    · simp [hx]
  right_inv v := by
    funext x
    simp [x.2]

/-- One function in `2 ^ #D` agrees with `g` on `D`. Stated multiplicatively to keep the
exponent free of truncated subtraction. -/
private lemma card_filter_agree_mul {α : Type*} [Fintype α] [DecidableEq α]
    (D : Finset α) (g : α → Bool) :
    #(univ.filter fun f : α → Bool => ∀ x ∈ D, f x = g x) * 2 ^ #D
      = 2 ^ Fintype.card α := by
  have hcard : #(univ.filter fun f : α → Bool => ∀ x ∈ D, f x = g x)
      = 2 ^ (Fintype.card α - #D) := by
    rw [← Fintype.card_subtype, Fintype.card_congr (agreeEquiv D g), Fintype.card_fun,
      Fintype.card_bool, Fintype.card_subtype_compl, Fintype.card_coe]
  rw [hcard, ← pow_add, Nat.sub_add_cancel (by simpa using Finset.card_le_univ D)]

/-- The ordered pairs of consecutive positions. -/
private def consecPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  univ.filter fun p => (p.2 : ℕ) = (p.1 : ℕ) + 1

private lemma card_consecPairs_le (n : ℕ) : #(consecPairs n) ≤ n - 1 := by
  classical
  have hinj : Set.InjOn (fun p : Fin n × Fin n => (p.1 : ℕ)) (consecPairs n) := by
    intro p hp q hq hpq
    simp only [consecPairs, mem_coe, mem_filter, mem_univ, true_and] at hp hq
    have hval : (p.1 : ℕ) = (q.1 : ℕ) := hpq
    have h1 : p.1 = q.1 := Fin.ext hval
    have h2 : p.2 = q.2 := Fin.ext (by omega)
    exact Prod.ext h1 h2
  have himg : (consecPairs n).image (fun p : Fin n × Fin n => (p.1 : ℕ))
      ⊆ Finset.range (n - 1) := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hx
    simp only [consecPairs, mem_filter, mem_univ, true_and] at hp
    have h2 := p.2.isLt
    exact Finset.mem_range.mpr (by omega)
  calc #(consecPairs n)
      = #((consecPairs n).image (fun p : Fin n × Fin n => (p.1 : ℕ))) :=
        (card_image_of_injOn hinj).symm
    _ ≤ #(Finset.range (n - 1)) := card_le_card himg
    _ = n - 1 := Finset.card_range _

/-- The edges an ordering constrains: the images of its consecutive pairs. -/
private def pathEdges (σ : Equiv.Perm (Fin n)) : Finset (Sym2 (Fin n)) :=
  (consecPairs n).image fun p => s(σ p.1, σ p.2)

private lemma card_pathEdges_le (σ : Equiv.Perm (Fin n)) : #(pathEdges σ) ≤ n - 1 :=
  le_trans card_image_le (card_consecPairs_le n)

/-- The tournament orienting every edge forwards along `σ`'s ordering. Written through
`min`/`max` so that symmetry in the two endpoints is immediate. -/
private def orient (σ : Equiv.Perm (Fin n)) : Sym2 (Fin n) → Bool :=
  Sym2.lift ⟨fun u v => decide (σ.symm (min u v) < σ.symm (max u v)), by
    intro u v
    show decide (σ.symm (min u v) < σ.symm (max u v))
        = decide (σ.symm (min v u) < σ.symm (max v u))
    rw [min_comm u v, max_comm u v]⟩

@[simp] private lemma orient_mk (σ : Equiv.Perm (Fin n)) (a b : Fin n) :
    orient σ s(a, b) = decide (σ.symm (min a b) < σ.symm (max a b)) := rfl

/-- Any tournament agreeing with `orient σ` on the edges `σ` constrains has `σ` as a
Hamilton path. Only agreement on those edges is needed, which is what makes the count a
power of two. -/
private lemma mem_hamiltonPaths_of_agree {t : Sym2 (Fin n) → Bool} {σ : Equiv.Perm (Fin n)}
    (h : ∀ x ∈ pathEdges σ, t x = orient σ x) : σ ∈ hamiltonPaths t := by
  rw [mem_hamiltonPaths]
  intro i j hij
  have hlt : i < j := by rw [Fin.lt_def]; omega
  have hmem : s(σ i, σ j) ∈ pathEdges σ := by
    refine mem_image.mpr ⟨(i, j), ?_, rfl⟩
    simp only [consecPairs, mem_filter, mem_univ, true_and]
    exact hij
  have ht := h _ hmem
  have hne : σ i ≠ σ j := fun hEq => absurd (σ.injective hEq) (ne_of_lt hlt)
  rcases lt_or_gt_of_ne hne with hab | hab
  · rw [beats, if_pos hab, ht, orient_mk, min_eq_left hab.le, max_eq_right hab.le,
      Equiv.symm_apply_apply, Equiv.symm_apply_apply, decide_eq_true_eq]
    exact hlt
  · rw [beats, if_neg (not_lt_of_gt hab), if_pos hab]
    have hx : s(σ j, σ i) = s(σ i, σ j) := Sym2.eq_swap
    rw [hx, ht, orient_mk, min_eq_right hab.le, max_eq_left hab.le,
      Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, not_lt]
    exact hlt.le

end Szele


/-- **Szele's theorem** (Zhao, Theorem 2.1.2; Szele 1943).

Some tournament on `n` vertices has at least `n! / 2 ^ (n - 1)` Hamilton paths.

Stated multiplicatively as `n ! ≤ #(hamiltonPaths t) * 2 ^ (n - 1)`, which says the same
thing while keeping the exponent free of truncated subtraction and the statement free of
division. This was, per the notes, the first use of the probabilistic method.

The book's proof orients every edge independently and uniformly at random. Each of the `n!`
orderings of the vertices is a Hamilton path with probability `2 ^ (1 - n)`, since it
constrains `n - 1` distinct edges, so the expected number of Hamilton paths is
`n ! * 2 ^ (1 - n)` and some tournament attains at least the mean. -/
theorem exists_tournament_factorial_le_hamiltonPaths (n : ℕ) :
    ∃ t : Sym2 (Fin n) → Bool, Nat.factorial n ≤ #(hamiltonPaths t) * 2 ^ (n - 1) := by
  classical
  -- For each ordering, at least `2 ^ (M - #pathEdges)` tournaments realise it.
  have hper : ∀ σ : Equiv.Perm (Fin n),
      2 ^ Fintype.card (Sym2 (Fin n))
        ≤ #(univ.filter fun t : Sym2 (Fin n) → Bool => σ ∈ hamiltonPaths t) * 2 ^ (n - 1) := by
    intro σ
    have hsub : (univ.filter fun t : Sym2 (Fin n) → Bool =>
          ∀ x ∈ pathEdges σ, t x = orient σ x)
        ⊆ univ.filter fun t : Sym2 (Fin n) → Bool => σ ∈ hamiltonPaths t := by
      intro t ht
      rw [mem_filter] at ht ⊢
      exact ⟨mem_univ _, mem_hamiltonPaths_of_agree ht.2⟩
    calc 2 ^ Fintype.card (Sym2 (Fin n))
        = #(univ.filter fun t : Sym2 (Fin n) → Bool =>
              ∀ x ∈ pathEdges σ, t x = orient σ x) * 2 ^ #(pathEdges σ) :=
          (card_filter_agree_mul _ _).symm
      _ ≤ #(univ.filter fun t : Sym2 (Fin n) → Bool =>
              ∀ x ∈ pathEdges σ, t x = orient σ x) * 2 ^ (n - 1) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (card_pathEdges_le σ))
      _ ≤ _ := Nat.mul_le_mul_right _ (card_le_card hsub)
  -- Exchange the order of summation.
  have hswap : ∑ t : Sym2 (Fin n) → Bool, #(hamiltonPaths t)
      = ∑ σ : Equiv.Perm (Fin n),
          #(univ.filter fun t : Sym2 (Fin n) → Bool => σ ∈ hamiltonPaths t) := by
    have hL : ∀ t : Sym2 (Fin n) → Bool,
        #(hamiltonPaths t)
          = ∑ σ : Equiv.Perm (Fin n), (if σ ∈ hamiltonPaths t then 1 else 0) := by
      intro t
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul, mul_one]
    have hR : ∀ σ : Equiv.Perm (Fin n),
        #(univ.filter fun t : Sym2 (Fin n) → Bool => σ ∈ hamiltonPaths t)
          = ∑ t : Sym2 (Fin n) → Bool, (if σ ∈ hamiltonPaths t then 1 else 0) :=
      fun σ => Finset.card_filter _ _
    calc ∑ t : Sym2 (Fin n) → Bool, #(hamiltonPaths t)
        = ∑ t : Sym2 (Fin n) → Bool, ∑ σ : Equiv.Perm (Fin n),
            (if σ ∈ hamiltonPaths t then 1 else 0) :=
          Finset.sum_congr rfl fun t _ => hL t
      _ = ∑ σ : Equiv.Perm (Fin n), ∑ t : Sym2 (Fin n) → Bool,
            (if σ ∈ hamiltonPaths t then 1 else 0) := Finset.sum_comm
      _ = _ := (Finset.sum_congr rfl fun σ _ => hR σ).symm

  -- Sum the per-ordering bound.
  have hsum : Nat.factorial n * 2 ^ Fintype.card (Sym2 (Fin n))
      ≤ (∑ t : Sym2 (Fin n) → Bool, #(hamiltonPaths t)) * 2 ^ (n - 1) := by
    rw [hswap, Finset.sum_mul]
    calc Nat.factorial n * 2 ^ Fintype.card (Sym2 (Fin n))
        = ∑ _σ : Equiv.Perm (Fin n), 2 ^ Fintype.card (Sym2 (Fin n)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
            smul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum fun σ _ => hper σ
  -- The maximum is at least the mean.
  obtain ⟨t₀, -, ht₀⟩ := Finset.exists_max_image (univ : Finset (Sym2 (Fin n) → Bool))
    (fun t => #(hamiltonPaths t)) ⟨fun _ => false, mem_univ _⟩
  refine ⟨t₀, ?_⟩
  have hmean : (∑ t : Sym2 (Fin n) → Bool, #(hamiltonPaths t))
      ≤ 2 ^ Fintype.card (Sym2 (Fin n)) * #(hamiltonPaths t₀) := by
    have h := Finset.sum_le_card_nsmul (univ : Finset (Sym2 (Fin n) → Bool))
      (fun t => #(hamiltonPaths t)) (#(hamiltonPaths t₀)) fun t ht => ht₀ t ht
    rwa [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, smul_eq_mul] at h
  have hchain : Nat.factorial n * 2 ^ Fintype.card (Sym2 (Fin n))
      ≤ 2 ^ Fintype.card (Sym2 (Fin n)) * (#(hamiltonPaths t₀) * 2 ^ (n - 1)) := by
    calc Nat.factorial n * 2 ^ Fintype.card (Sym2 (Fin n))
        ≤ (∑ t : Sym2 (Fin n) → Bool, #(hamiltonPaths t)) * 2 ^ (n - 1) := hsum
      _ ≤ 2 ^ Fintype.card (Sym2 (Fin n)) * #(hamiltonPaths t₀) * 2 ^ (n - 1) :=
          Nat.mul_le_mul_right _ hmean
      _ = 2 ^ Fintype.card (Sym2 (Fin n)) * (#(hamiltonPaths t₀) * 2 ^ (n - 1)) :=
          mul_assoc _ _ _
  have hpos : 0 < 2 ^ Fintype.card (Sym2 (Fin n)) := Nat.two_pow_pos _
  rw [mul_comm (Nat.factorial n)] at hchain
  exact Nat.le_of_mul_le_mul_left hchain hpos

end PMC
