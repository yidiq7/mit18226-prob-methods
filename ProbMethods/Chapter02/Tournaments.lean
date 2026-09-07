import ProbMethods.Basic
import Mathlib.Data.Sym.Sym2.Order
import Mathlib.Data.Fintype.BigOperators
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

/-- The functions agreeing with `v` on `S` are exactly the functions on the complement of
`S`, extended by `v`. -/
private def agreeEquiv {β : Type*} [Fintype β] [DecidableEq β] (S : Finset β) (v : β → Bool) :
    {f : β → Bool // ∀ x ∈ S, f x = v x} ≃ ({x : β // x ∉ S} → Bool) where
  toFun f x := f.1 x.1
  invFun u := ⟨fun x => if h : x ∈ S then v x else u ⟨x, h⟩, fun x hx => by simp [hx]⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ S
    · simp [hx, f.2 x hx]
    · simp [hx]
  right_inv u := by funext x; simp [x.2]

/-- One function in `2 ^ #S` agrees with `v` on `S`. Unlike the constant-value count used in
§1.1, each element of `S` here carries its own prescribed value. -/
private lemma card_filter_agree_mul {β : Type*} [Fintype β] [DecidableEq β]
    (S : Finset β) (v : β → Bool) :
    #(univ.filter fun f : β → Bool => ∀ x ∈ S, f x = v x) * 2 ^ #S = 2 ^ Fintype.card β := by
  have hcard : #(univ.filter fun f : β → Bool => ∀ x ∈ S, f x = v x)
      = 2 ^ (Fintype.card β - #S) := by
    rw [← Fintype.card_subtype, Fintype.card_congr (agreeEquiv S v), Fintype.card_fun,
      Fintype.card_bool, Fintype.card_subtype_compl, Fintype.card_coe]
  rw [hcard, ← pow_add, Nat.sub_add_cancel (by simpa using Finset.card_le_univ S)]

/-- `a` beats `b` exactly when `t` takes a prescribed value on the edge `s(a, b)`. -/
private lemma beats_iff_eq (t : Sym2 (Fin n) → Bool) {a b : Fin n} (h : a ≠ b) :
    beats t a b = true ↔ t s(a, b) = decide (a < b) := by
  rcases lt_or_gt_of_ne h with hab | hab
  · simp [beats, hab]
  · rw [Sym2.eq_swap]
    simp [beats, not_lt_of_gt hab, hab]

/-- The source vertex index of the `k`-th step of a path on `Fin n`. -/
private def stepSrc (n : ℕ) (k : Fin (n - 1)) : Fin n := ⟨(k : ℕ), by have := k.isLt; omega⟩

/-- The target vertex index of the `k`-th step. -/
private def stepTgt (n : ℕ) (k : Fin (n - 1)) : Fin n := ⟨(k : ℕ) + 1, by have := k.isLt; omega⟩

/-- The `n - 1` edges on which `σ` being a Hamilton path constrains the tournament. -/
private def pathEdges (σ : Equiv.Perm (Fin n)) : Finset (Sym2 (Fin n)) :=
  univ.image fun k : Fin (n - 1) => s(σ (stepSrc n k), σ (stepTgt n k))

/-- The value the tournament must take on an edge for `σ` to traverse it forwards. -/
private def pathValue (σ : Equiv.Perm (Fin n)) (e : Sym2 (Fin n)) : Bool :=
  decide (σ.symm e.inf < σ.symm e.sup)

private lemma pathValue_mk (σ : Equiv.Perm (Fin n)) {a b : Fin n} (hab : σ.symm a < σ.symm b) :
    pathValue σ s(a, b) = decide (a < b) := by
  rcases lt_trichotomy a b with h | h | h
  · simp [pathValue, inf_eq_left.mpr h.le, sup_eq_right.mpr h.le, hab, h]
  · exact absurd (h ▸ hab) (lt_irrefl _)
  · simp [pathValue, inf_eq_right.mpr h.le, sup_eq_left.mpr h.le, not_lt_of_gt hab,
      not_lt_of_gt h]

/-- The steps of a path use distinct edges, because the path visits distinct vertices. -/
private lemma card_pathEdges (σ : Equiv.Perm (Fin n)) : #(pathEdges σ) = n - 1 := by
  have hinj : Function.Injective
      (fun k : Fin (n - 1) => s(σ (stepSrc n k), σ (stepTgt n k))) := by
    intro k k' hkk'
    rcases Sym2.eq_iff.mp hkk' with ⟨h1, -⟩ | ⟨h1, h2⟩
    · have := congrArg Fin.val (σ.injective h1)
      exact Fin.ext (by simpa [stepSrc] using this)
    · have v1 := congrArg Fin.val (σ.injective h1)
      have v2 := congrArg Fin.val (σ.injective h2)
      simp only [stepSrc, stepTgt] at v1 v2
      omega
  rw [pathEdges, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

/-- Being a Hamilton path for `σ` is exactly a prescription of `t` on `pathEdges σ`. -/
private lemma mem_hamiltonPaths_iff (t : Sym2 (Fin n) → Bool) (σ : Equiv.Perm (Fin n)) :
    σ ∈ hamiltonPaths t ↔ ∀ e ∈ pathEdges σ, t e = pathValue σ e := by
  rw [mem_hamiltonPaths]
  constructor
  · intro h e he
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp he
    have hstep : ((stepTgt n k : Fin n) : ℕ) = ((stepSrc n k : Fin n) : ℕ) + 1 := rfl
    have hne : σ (stepSrc n k) ≠ σ (stepTgt n k) := by
      intro he'
      have := congrArg Fin.val (σ.injective he')
      simp only [stepSrc, stepTgt] at this
      omega
    have hb := (beats_iff_eq t hne).mp (h _ _ hstep)
    have hlt : σ.symm (σ (stepSrc n k)) < σ.symm (σ (stepTgt n k)) := by
      simp only [Equiv.symm_apply_apply]
      exact Fin.lt_def.mpr (by simp [stepSrc, stepTgt])
    rw [hb, pathValue_mk σ hlt]
  · intro h i j hij
    have hi : (i : ℕ) < n - 1 := by have := j.isLt; omega
    set k : Fin (n - 1) := ⟨(i : ℕ), hi⟩ with hk
    have hsrc : stepSrc n k = i := Fin.ext rfl
    have htgt : stepTgt n k = j := Fin.ext (by simp [stepTgt, hk, hij])
    have hmem : s(σ (stepSrc n k), σ (stepTgt n k)) ∈ pathEdges σ :=
      Finset.mem_image_of_mem _ (mem_univ k)
    have hval := h _ hmem
    have hlt : σ.symm (σ (stepSrc n k)) < σ.symm (σ (stepTgt n k)) := by
      simp only [Equiv.symm_apply_apply, hsrc, htgt]
      exact Fin.lt_def.mpr (by omega)
    rw [pathValue_mk σ hlt] at hval
    have hne : σ (stepSrc n k) ≠ σ (stepTgt n k) := by
      intro he'
      have := congrArg Fin.val (σ.injective he')
      simp only [stepSrc, stepTgt] at this
      omega
    rw [hsrc, htgt] at hval hne
    exact (beats_iff_eq t hne).mpr hval

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
  obtain ⟨t₀, -, ht₀⟩ := Finset.exists_max_image (univ : Finset (Sym2 (Fin n) → Bool))
    (fun t => #(hamiltonPaths t)) univ_nonempty
  refine ⟨t₀, ?_⟩
  -- for a fixed ordering, one tournament in `2 ^ (n - 1)` makes it a Hamilton path
  have hcount : ∀ σ : Equiv.Perm (Fin n),
      #(univ.filter fun t : Sym2 (Fin n) → Bool => σ ∈ hamiltonPaths t) * 2 ^ (n - 1)
        = 2 ^ Fintype.card (Sym2 (Fin n)) := by
    intro σ
    have hset : (univ.filter fun t : Sym2 (Fin n) → Bool => σ ∈ hamiltonPaths t)
        = (univ.filter fun t : Sym2 (Fin n) → Bool => ∀ e ∈ pathEdges σ, t e = pathValue σ e) := by
      ext t
      simp only [mem_filter, mem_univ, true_and]
      exact mem_hamiltonPaths_iff t σ
    rw [hset, ← card_pathEdges σ]
    exact card_filter_agree_mul _ _
  -- exchange the order of summation
  have hswap : (∑ t : Sym2 (Fin n) → Bool, #(hamiltonPaths t)) * 2 ^ (n - 1)
      = Nat.factorial n * 2 ^ Fintype.card (Sym2 (Fin n)) := by
    have e1 : ∀ t : Sym2 (Fin n) → Bool,
        #(hamiltonPaths t)
          = #(univ.filter fun σ : Equiv.Perm (Fin n) => σ ∈ hamiltonPaths t) := by
      intro t
      congr 1
      ext σ
      simp
    rw [Finset.sum_congr rfl fun t _ => e1 t]
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    simp only [← Finset.card_filter]
    rw [Finset.sum_mul, Finset.sum_congr rfl fun σ _ => hcount σ, Finset.sum_const,
      Finset.card_univ, Fintype.card_perm, Fintype.card_fin, smul_eq_mul]
  -- the maximum is at least the mean
  have hmean : ∑ t : Sym2 (Fin n) → Bool, #(hamiltonPaths t)
      ≤ 2 ^ Fintype.card (Sym2 (Fin n)) * #(hamiltonPaths t₀) := by
    calc ∑ t : Sym2 (Fin n) → Bool, #(hamiltonPaths t)
        ≤ ∑ _t : Sym2 (Fin n) → Bool, #(hamiltonPaths t₀) :=
          Finset.sum_le_sum fun t _ => ht₀ t (mem_univ t)
      _ = 2 ^ Fintype.card (Sym2 (Fin n)) * #(hamiltonPaths t₀) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
            smul_eq_mul]
  have hpos : 0 < 2 ^ Fintype.card (Sym2 (Fin n)) := pow_pos (by norm_num) _
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  calc 2 ^ Fintype.card (Sym2 (Fin n)) * Nat.factorial n
      = Nat.factorial n * 2 ^ Fintype.card (Sym2 (Fin n)) := Nat.mul_comm _ _
    _ = (∑ t : Sym2 (Fin n) → Bool, #(hamiltonPaths t)) * 2 ^ (n - 1) := hswap.symm
    _ ≤ 2 ^ Fintype.card (Sym2 (Fin n)) * #(hamiltonPaths t₀) * 2 ^ (n - 1) :=
        Nat.mul_le_mul_right _ hmean
    _ = 2 ^ Fintype.card (Sym2 (Fin n)) * (#(hamiltonPaths t₀) * 2 ^ (n - 1)) :=
        Nat.mul_assoc _ _ _

end PMC
