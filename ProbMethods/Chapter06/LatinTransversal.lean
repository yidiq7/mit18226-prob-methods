import ProbMethods.Permutation
import ProbMethods.Chapter06.LocalLemma
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# §6.5 — Latin transversals (Theorem 6.5.11)

Zhao, *Probabilistic Methods in Combinatorics*, Theorem 6.5.11 (Erdős and Spencer 1991):
every `n × n` array in which every entry appears at most `n/(4e)` times has a **Latin
transversal** — a system of `n` cells, one per row and one per column, with distinct entries.

This is the original application of the lopsided local lemma. A transversal is a permutation
`σ`, the bad events are "the transversal uses both cells of a pair of equal entries", and the
dependency neighbourhood joins two bad pairs when their four cells share a row or a column.

## What is proved and what is assumed

The two inputs the notes use are:

* the probability `P(σ i₁ = j₁ ∧ σ i₂ = j₂) = 1/(n(n-1))` — proved, `PMC.wprob_pairEvent`;
* the *negative dependence* of these events under a uniform random permutation, which is
  Theorem 6.5.5 for the random injection model.

Theorem 6.5.5 in full generality needs the permutation carrying one matching to another while
fixing everything else (`PMC.exists_perm_extend`, still open), so it is taken here as an
explicit hypothesis `hlop` — exactly the hypothesis `PMC.lovasz_local_lemma_symmetric_lopsided`
consumes. Everything else in the notes' proof is discharged: the degree count and the
arithmetic that makes `e p (d+1) ≤ 1` come out.

## The degree count

The notes bound the degree by `(4n-4)(n/(4e) - 1)`: the two cells' rows and columns span fewer
than `4n` cells, and each such cell `z` has at most `n/(4e) - 1` partners carrying the same
entry. The crude `4n` in place of `4n - 4` is enough here — the slack in `e p (d+1) ≤ 1` is a
factor `4en` against `n`, so four rows' worth of cells costs nothing — and it makes the count
a union bound over four lines of the array rather than an inclusion–exclusion.

Each unordered bad pair is one index, obtained by orienting the pair as `i₁ < i₂`; indexing by
*ordered* pairs would list every bad event twice and double the degree, which the constant
does not survive.
-/

open Finset

namespace PMC

section LatinTransversal

variable {n : ℕ} {κ : Type*} [DecidableEq κ]

/-- The cells carrying the entry `z`. -/
def cellsWith (c : Fin n → Fin n → κ) (z : κ) : Finset (Fin n × Fin n) :=
  (univ : Finset (Fin n × Fin n)).filter fun q => c q.1 q.2 = z

lemma mem_cellsWith {c : Fin n → Fin n → κ} {z : κ} {q : Fin n × Fin n} :
    q ∈ cellsWith c z ↔ c q.1 q.2 = z := by
  rw [cellsWith, mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩

/-- A *bad pair*: two cells in different rows and different columns carrying the same entry,
oriented by `i₁ < i₂` so that each unordered pair is a single index. -/
def IsBadPair (c : Fin n → Fin n → κ) (p : (Fin n × Fin n) × (Fin n × Fin n)) : Prop :=
  p.1.1 < p.2.1 ∧ p.1.2 ≠ p.2.2 ∧ c p.1.1 p.1.2 = c p.2.1 p.2.2

instance (c : Fin n → Fin n → κ) : DecidablePred (IsBadPair c) := fun p => by
  rw [IsBadPair]
  infer_instance

/-- The bad event of `p`: the transversal uses both of `p`'s cells. Non-bad indices carry the
empty event, so the index type can be all pairs of cells. -/
def badTransversal (c : Fin n → Fin n → κ) (p : (Fin n × Fin n) × (Fin n × Fin n)) :
    Finset (Equiv.Perm (Fin n)) :=
  if IsBadPair c p then pairEvent p.1.1 p.1.2 p.2.1 p.2.2 else ∅

/-- The cells sharing a row or a column with one of `p`'s cells: four lines of the array. -/
def crossCells (p : (Fin n × Fin n) × (Fin n × Fin n)) : Finset (Fin n × Fin n) :=
  ({p.1.1, p.2.1} ×ˢ (univ : Finset (Fin n))) ∪ ((univ : Finset (Fin n)) ×ˢ {p.1.2, p.2.2})

lemma card_crossCells_le (p : (Fin n × Fin n) × (Fin n × Fin n)) :
    #(crossCells p) ≤ 4 * n := by
  classical
  calc #(crossCells p)
      ≤ #(({p.1.1, p.2.1} : Finset (Fin n)) ×ˢ (univ : Finset (Fin n)))
          + #((univ : Finset (Fin n)) ×ˢ ({p.1.2, p.2.2} : Finset (Fin n))) :=
        Finset.card_union_le _ _
    _ ≤ 2 * n + n * 2 := by
        rw [Finset.card_product, Finset.card_product, card_univ, Fintype.card_fin]
        exact Nat.add_le_add
          (Nat.mul_le_mul_right n (le_trans (Finset.card_insert_le _ _) (by simp)))
          (Nat.mul_le_mul_left n (le_trans (Finset.card_insert_le _ _) (by simp)))
    _ = 4 * n := by ring

lemma mem_crossCells {p : (Fin n × Fin n) × (Fin n × Fin n)} {q : Fin n × Fin n} :
    q ∈ crossCells p ↔ (q.1 = p.1.1 ∨ q.1 = p.2.1) ∨ (q.2 = p.1.2 ∨ q.2 = p.2.2) := by
  simp [crossCells, Finset.mem_union, Finset.mem_product]

/-- The dependency neighbourhood: the other bad pairs one of whose cells meets `p`'s rows or
columns. -/
def badNbrs (c : Fin n → Fin n → κ) (p : (Fin n × Fin n) × (Fin n × Fin n)) :
    Finset ((Fin n × Fin n) × (Fin n × Fin n)) :=
  (univ : Finset ((Fin n × Fin n) × (Fin n × Fin n))).filter fun q =>
    q ≠ p ∧ IsBadPair c q ∧ (q.1 ∈ crossCells p ∨ q.2 ∈ crossCells p)

lemma mem_badNbrs {c : Fin n → Fin n → κ} {p q : (Fin n × Fin n) × (Fin n × Fin n)} :
    q ∈ badNbrs c p ↔
      q ≠ p ∧ IsBadPair c q ∧ (q.1 ∈ crossCells p ∨ q.2 ∈ crossCells p) := by
  rw [badNbrs, mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩

/-- The oriented pair built from two cells in different rows. -/
def orientPair (z z' : Fin n × Fin n) : (Fin n × Fin n) × (Fin n × Fin n) :=
  if z.1 < z'.1 then (z, z') else (z', z)

/-- **The degree count.** If every entry appears at most `m` times, a bad pair meets at most
`4n(m-1)` others — one of the neighbour's two cells lies on one of `p`'s four lines, and the
other is one of the at most `m - 1` remaining cells with that entry. -/
lemma card_badNbrs_le {c : Fin n → Fin n → κ} {m : ℕ} (hm : ∀ z, #(cellsWith c z) ≤ m)
    (p : (Fin n × Fin n) × (Fin n × Fin n)) :
    #(badNbrs c p) ≤ 4 * n * (m - 1) := by
  classical
  have hsub : badNbrs c p ⊆ (crossCells p).biUnion fun z =>
      ((cellsWith c (c z.1 z.2)).erase z).image fun z' => orientPair z z' := by
    intro q hq
    rw [mem_badNbrs] at hq
    obtain ⟨-, hbad, hcross⟩ := hq
    have hlt : q.1.1 < q.2.1 := hbad.1
    have hentry : c q.1.1 q.1.2 = c q.2.1 q.2.2 := hbad.2.2
    have hrow : q.1.1 ≠ q.2.1 := ne_of_lt hlt
    have hq12 : q.1 ≠ q.2 := fun h => hrow (congrArg Prod.fst h)
    have horient : orientPair q.1 q.2 = q := by
      rw [orientPair, if_pos hlt]
    rcases hcross with h1 | h2
    · refine Finset.mem_biUnion.mpr ⟨q.1, h1, Finset.mem_image.mpr ⟨q.2, ?_, horient⟩⟩
      exact Finset.mem_erase.mpr ⟨Ne.symm hq12, mem_cellsWith.mpr hentry.symm⟩
    · refine Finset.mem_biUnion.mpr ⟨q.2, h2, Finset.mem_image.mpr ⟨q.1, ?_, ?_⟩⟩
      · exact Finset.mem_erase.mpr ⟨hq12, mem_cellsWith.mpr hentry⟩
      · rw [orientPair, if_neg (not_lt_of_gt hlt)]
  calc #(badNbrs c p)
      ≤ ∑ z ∈ crossCells p,
          #(((cellsWith c (c z.1 z.2)).erase z).image fun z' => orientPair z z') :=
        le_trans (Finset.card_le_card hsub) (Finset.card_biUnion_le)
    _ ≤ ∑ _z ∈ crossCells p, (m - 1) := by
        refine Finset.sum_le_sum fun z _ => ?_
        refine le_trans Finset.card_image_le ?_
        rw [Finset.card_erase_of_mem (mem_cellsWith.mpr rfl)]
        exact Nat.sub_le_sub_right (hm _) 1
    _ = #(crossCells p) * (m - 1) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 4 * n * (m - 1) := Nat.mul_le_mul_right _ (card_crossCells_le p)


/-- **Theorem 6.5.11** (Erdős and Spencer 1991). If every entry of an `n × n` array appears at
most `m` times and `4 e m ≤ n`, then the array has a Latin transversal: a permutation `σ` with
`c i (σ i)` pairwise distinct.

`hlop` is the negative-dependence input, Theorem 6.5.5 for the random injection model; it is
the hypothesis `PMC.lovasz_local_lemma_symmetric_lopsided` consumes and waits on
`PMC.exists_perm_extend`. Everything else is discharged here: `PMC.wprob_pairEvent` for the
probability `1/(n(n-1))`, `PMC.card_badNbrs_le` for the degree, and the arithmetic

    e · (4n(m-1) + 2) ≤ n(n-1),

which is where `4 e m ≤ n` is used and why the crude degree bound suffices. -/
theorem exists_latin_transversal {c : Fin n → Fin n → κ} {m : ℕ}
    (hm : ∀ z, #(cellsWith c z) ≤ m) (hmn : 4 * Real.exp 1 * (m : ℝ) ≤ n)
    (hlop : ∀ (p : (Fin n × Fin n) × (Fin n × Fin n))
      (T : Finset ((Fin n × Fin n) × (Fin n × Fin n))),
      Disjoint T (insert p (badNbrs c p)) →
      wprob (unifPerm (Fin n)) (badTransversal c p ∩ noneOf (badTransversal c) T)
        ≤ wprob (unifPerm (Fin n)) (badTransversal c p)
          * wprob (unifPerm (Fin n)) (noneOf (badTransversal c) T)) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i₁ i₂, i₁ ≠ i₂ → c i₁ (σ i₁) ≠ c i₂ (σ i₂) := by
  classical
  rcases Nat.lt_or_ge n 2 with hn | hn
  · -- fewer than two rows: there are no two distinct rows to compare
    refine ⟨1, fun i₁ i₂ hne => absurd (Fin.ext ?_) hne⟩
    have h1 := i₁.isLt
    have h2 := i₂.isLt
    omega
  have : NeZero n := ⟨by omega⟩
  -- the entry of any one cell already forces `1 ≤ m`
  have hmpos : 1 ≤ m := by
    have hbound := hm (c (0 : Fin n) (0 : Fin n))
    have hpos : 0 < #(cellsWith c (c (0 : Fin n) (0 : Fin n))) :=
      card_pos.mpr ⟨((0 : Fin n), (0 : Fin n)), mem_cellsWith.mpr rfl⟩
    omega
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have he : (2.7 : ℝ) < Real.exp 1 := by
    have := Real.exp_one_gt_d9
    norm_num at this ⊢
    linarith
  have hmR : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    have : (1 : ℕ) ≤ m := hmpos
    push_cast [this]
    ring
  set d : ℕ := 4 * n * (m - 1) + 1 with hddef
  set p₀ : ℝ := 1 / ((n : ℝ) * ((n : ℝ) - 1)) with hp₀def
  have hden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
  have hp₀0 : 0 ≤ p₀ := by
    rw [hp₀def]
    positivity
  -- each bad event has probability exactly `1/(n(n-1))`
  have hprob : ∀ q, wprob (unifPerm (Fin n)) (badTransversal c q) ≤ p₀ := by
    intro q
    by_cases hq : IsBadPair c q
    · rw [badTransversal, if_pos hq,
        wprob_pairEvent (ne_of_lt hq.1) (Ne.symm hq.2.1), Fintype.card_fin]
    · rw [badTransversal, if_neg hq, wprob_empty]
      exact hp₀0
  -- the arithmetic side condition
  have hep : Real.exp 1 * p₀ * ((d : ℝ) + 1) ≤ 1 := by
    have hdR : (d : ℝ) + 1 = 4 * (n : ℝ) * ((m : ℝ) - 1) + 2 := by
      rw [hddef]
      push_cast [hmR]
      ring
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by linarith
    have hmul : (n : ℝ) * (4 * Real.exp 1 * (m : ℝ)) ≤ (n : ℝ) * (n : ℝ) :=
      mul_le_mul_of_nonneg_left hmn hn0
    have hkey : Real.exp 1 * (4 * (n : ℝ) * ((m : ℝ) - 1) + 2)
        ≤ (n : ℝ) * ((n : ℝ) - 1) := by
      nlinarith [hmul, he, hnR, Real.exp_pos 1]
    rw [hp₀def, hdR]
    calc Real.exp 1 * (1 / ((n : ℝ) * ((n : ℝ) - 1))) * (4 * (n : ℝ) * ((m : ℝ) - 1) + 2)
        = (Real.exp 1 * (4 * (n : ℝ) * ((m : ℝ) - 1) + 2)) / ((n : ℝ) * ((n : ℝ) - 1)) := by
          ring
      _ ≤ 1 := by
          rw [div_le_one hden]
          exact hkey
  have hpos := lovasz_local_lemma_symmetric_lopsided (unifPerm (Fin n))
    (unifPerm_nonneg) (sum_unifPerm) (badTransversal c) (badNbrs c)
    (d := d) (by rw [hddef]; omega) hp₀0
    (fun q => by
      rw [mem_badNbrs]
      exact fun h => h.1 rfl)
    (fun q => le_trans (card_badNbrs_le hm q) (by rw [hddef]; omega))
    hlop hprob hep
  -- a positive-probability event has a member, and its members are the Latin transversals
  have hne : (noneOf (badTransversal c) (univ : Finset ((Fin n × Fin n) × (Fin n × Fin n)))).Nonempty := by
    rcases Finset.eq_empty_or_nonempty
      (noneOf (badTransversal c) (univ : Finset ((Fin n × Fin n) × (Fin n × Fin n)))) with h | h
    · rw [h, wprob_empty] at hpos
      linarith
    · exact h
  obtain ⟨σ, hσ⟩ := hne
  refine ⟨σ, fun i₁ i₂ hne heq => ?_⟩
  -- the two cells of a repeated entry would be a bad pair the transversal uses
  have key : ∀ a b : Fin n, a < b → c a (σ a) = c b (σ b) → False := by
    intro a b hab hval
    have hbad : IsBadPair c ((a, σ a), (b, σ b)) :=
      ⟨hab, fun h => absurd (σ.injective h) (ne_of_lt hab), hval⟩
    have hmem : σ ∈ badTransversal c ((a, σ a), (b, σ b)) := by
      rw [badTransversal, if_pos hbad, pairEvent, mem_filter]
      exact ⟨mem_univ _, rfl, rfl⟩
    exact mem_noneOf.mp hσ _ (mem_univ _) hmem
  rcases lt_or_gt_of_ne hne with h | h
  · exact key i₁ i₂ h heq
  · exact key i₂ i₁ h heq.symm

end LatinTransversal

end PMC
