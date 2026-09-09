import ProbMethods.Chapter02.Tournaments
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# §10.2 — from Hamilton paths to Hamilton cycles (Lemma 10.2.7)

Zhao, *Probabilistic Methods in Combinatorics*, Lemma 10.2.7: an `n`-vertex tournament with
`P` Hamilton paths can be extended by one vertex to an `(n+1)`-vertex tournament with at
least `P/4` Hamilton cycles. Together with Szele's theorem
(`PMC.exists_tournament_factorial_le_hamiltonPaths`) this is the lower bound half of
Theorem 10.2.4.

Stated multiplicatively as `P ≤ 4 · #cycles`, which keeps the statement free of division.

`2 ≤ n` is necessary, not cosmetic: for `n = 1` the notes' argument closes the one-vertex
path through the new vertex by orienting *the same edge* both ways, which happens with
probability `0` rather than `1/4` — and indeed a `2`-vertex tournament has no Hamilton cycle
at all, while it does have a Hamilton path.

## Counting cycles

A directed Hamilton cycle passes through each vertex exactly once, so fixing a vertex and
counting the orderings that *start* there counts each cycle exactly once
(`PMC.hamCycles`). Taking that vertex to be the newly added one is what makes the extension
step a statement about orderings of the old vertices.
-/

open Finset

namespace PMC

section HamCycles

variable {n : ℕ}

/-- The tournament on `Fin (n+1)` extending `t` by a new vertex `Fin.last n`, whose incident
edges are oriented by `o`: the new vertex is beaten by `a` exactly when `o a` is `true`. -/
def extendT (t : Sym2 (Fin n) → Bool) (o : Fin n → Bool) : Sym2 (Fin (n + 1)) → Bool :=
  Sym2.lift ⟨fun u v =>
    Fin.lastCases (Fin.lastCases false (fun b => o b) v)
      (fun a => Fin.lastCases (o a) (fun b => t s(a, b)) v) u, by
    intro u v
    induction u using Fin.lastCases <;> induction v using Fin.lastCases <;>
      simp [Sym2.eq_swap]⟩

@[simp] lemma extendT_castSucc_castSucc (t : Sym2 (Fin n) → Bool) (o : Fin n → Bool)
    (a b : Fin n) : extendT t o s(a.castSucc, b.castSucc) = t s(a, b) := by
  simp [extendT]

@[simp] lemma extendT_castSucc_last (t : Sym2 (Fin n) → Bool) (o : Fin n → Bool) (a : Fin n) :
    extendT t o s(a.castSucc, Fin.last n) = o a := by
  simp [extendT]

lemma beats_extendT_castSucc (t : Sym2 (Fin n) → Bool) (o : Fin n → Bool) (a b : Fin n) :
    beats (extendT t o) a.castSucc b.castSucc = beats t a b := by
  simp only [beats, Fin.castSucc_lt_castSucc_iff]
  by_cases hab : a < b
  · simp [hab]
  · by_cases hba : b < a
    · simp [hab, hba]
    · simp [hab, hba]

lemma beats_extendT_last (t : Sym2 (Fin n) → Bool) (o : Fin n → Bool) (a : Fin n) :
    beats (extendT t o) a.castSucc (Fin.last n) = o a := by
  rw [beats, if_pos (Fin.castSucc_lt_last a), extendT_castSucc_last]

lemma beats_extendT_last' (t : Sym2 (Fin n) → Bool) (o : Fin n → Bool) (a : Fin n) :
    beats (extendT t o) (Fin.last n) a.castSucc = !o a := by
  rw [beats, if_neg (not_lt_of_gt (Fin.castSucc_lt_last a)),
    if_pos (Fin.castSucc_lt_last a), extendT_castSucc_last]


/-! ### Hamilton cycles, and closing up a path -/

/-- The Hamilton cycles of a tournament on `Fin (n+1)`, counted as the orderings that start
at `Fin.last n`. A directed Hamilton cycle meets every vertex once, so it is exactly one such
ordering, and this is an honest count of the cycles. -/
def hamCycles (t : Sym2 (Fin (n + 1)) → Bool) : Finset (Equiv.Perm (Fin (n + 1))) :=
  univ.filter fun τ => τ 0 = Fin.last n ∧ ∀ i : Fin (n + 1), beats t (τ i) (τ (i + 1))

@[simp] lemma mem_hamCycles {t : Sym2 (Fin (n + 1)) → Bool} {τ : Equiv.Perm (Fin (n + 1))} :
    τ ∈ hamCycles t ↔ τ 0 = Fin.last n ∧ ∀ i : Fin (n + 1), beats t (τ i) (τ (i + 1)) := by
  simp [hamCycles]

private lemma cycleOf_injective (σ : Equiv.Perm (Fin n)) :
    Function.Injective (Fin.cases (motive := fun _ => Fin (n + 1)) (Fin.last n)
      fun i => (σ i).castSucc) := by
  intro u v h
  induction u using Fin.cases with
  | zero =>
    induction v using Fin.cases with
    | zero => rfl
    | succ j =>
      simp only [Fin.cases_zero, Fin.cases_succ] at h
      exact absurd h.symm (Fin.castSucc_lt_last _).ne
  | succ i =>
    induction v using Fin.cases with
    | zero =>
      simp only [Fin.cases_zero, Fin.cases_succ] at h
      exact absurd h (Fin.castSucc_lt_last _).ne
    | succ j =>
      simp only [Fin.cases_succ] at h
      exact congrArg Fin.succ (σ.injective (Fin.castSucc_injective n h))

/-- The cycle obtained by closing the path `σ` up through the new vertex: it starts at
`Fin.last n` and then follows `σ`. -/
noncomputable def cycleOf (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.ofBijective _ (Finite.injective_iff_bijective.mp (cycleOf_injective σ))

@[simp] lemma cycleOf_zero (σ : Equiv.Perm (Fin n)) : cycleOf σ 0 = Fin.last n := rfl

@[simp] lemma cycleOf_succ (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    cycleOf σ i.succ = (σ i).castSucc := rfl

lemma cycleOf_injOn : Function.Injective (cycleOf (n := n)) := by
  intro σ τ h
  refine Equiv.ext fun i => ?_
  have hi : cycleOf σ i.succ = cycleOf τ i.succ := by rw [h]
  rw [cycleOf_succ, cycleOf_succ] at hi
  exact Fin.castSucc_injective n hi

/-- **Closing up a Hamilton path.** If the new vertex is oriented to receive the path's last
vertex (`o (σ (last)) = true`) and to feed its first (`o (σ 0) = false`), then `cycleOf σ` is
a Hamilton cycle of the extended tournament.

The three cases are the two new edges and the old path edges; the `Fin` bookkeeping is where
`i + 1` wraps (at `i = Fin.last (m+1)`, giving the edge back to the new vertex) and where it
does not. -/
lemma cycleOf_mem_hamCycles {m : ℕ} (t : Sym2 (Fin (m + 1)) → Bool) (o : Fin (m + 1) → Bool)
    {σ : Equiv.Perm (Fin (m + 1))} (hσ : σ ∈ hamiltonPaths t)
    (hend : o (σ (Fin.last m)) = true) (hstart : o (σ 0) = false) :
    cycleOf σ ∈ hamCycles (extendT t o) := by
  rw [mem_hamCycles]
  refine ⟨cycleOf_zero σ, fun i => ?_⟩
  induction i using Fin.cases with
  | zero =>
    have h1 : (0 : Fin (m + 2)) + 1 = (0 : Fin (m + 1)).succ := by
      rw [Fin.ext_iff]
      simp
    rw [h1, cycleOf_zero, cycleOf_succ, beats_extendT_last', hstart]
    rfl
  | succ j =>
    induction j using Fin.lastCases with
    | last =>
      have h1 : (Fin.last m).succ + 1 = (0 : Fin (m + 2)) := by
        rw [Fin.succ_last]
        exact Fin.last_add_one _
      rw [h1, cycleOf_zero, cycleOf_succ, beats_extendT_last, hend]
    | cast k =>
      have h1 : (k.castSucc : Fin (m + 1)).succ + 1 = (k.succ : Fin (m + 1)).succ := by
        rw [Fin.ext_iff, Fin.val_add_one_of_lt, Fin.val_succ, Fin.val_succ, Fin.val_succ,
          Fin.val_castSucc]
        · rw [Fin.lt_def, Fin.val_succ, Fin.val_castSucc, Fin.val_last]
          omega
      rw [h1, cycleOf_succ, cycleOf_succ, beats_extendT_castSucc]
      exact mem_hamiltonPaths.mp hσ _ _ (by simp)


/-! ### The averaging argument -/

/-- The orientations of the new vertex's edges that close the path `σ` up into a cycle. -/
def closingOrients {m : ℕ} (σ : Equiv.Perm (Fin (m + 1))) : Finset (Fin (m + 1) → Bool) :=
  (univ : Finset (Fin (m + 1) → Bool)).filter fun o =>
    o (σ (Fin.last m)) = true ∧ o (σ 0) = false

/-- **One orientation in four closes a given path.** Two of the `n` new edges are
constrained, in opposite directions, and the path's two ends are distinct exactly because
`n ≥ 2`. -/
lemma card_closingOrients_mul {m : ℕ} (hm : 1 ≤ m) (σ : Equiv.Perm (Fin (m + 1))) :
    #(closingOrients σ) * 4 = 2 ^ (m + 1) := by
  have hne : σ 0 ≠ σ (Fin.last m) := by
    intro h
    have h0 := congrArg Fin.val (σ.injective h)
    simp only [Fin.val_zero, Fin.val_last] at h0
    omega
  have hcardD : #({σ 0, σ (Fin.last m)} : Finset (Fin (m + 1))) = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]
  have hfilter : closingOrients σ
      = (univ : Finset (Fin (m + 1) → Bool)).filter
          fun o => ∀ x ∈ ({σ 0, σ (Fin.last m)} : Finset (Fin (m + 1))),
            o x = decide (x = σ (Fin.last m)) := by
    ext o
    simp only [closingOrients, mem_filter, mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro h x hx
      rcases hx with rfl | rfl
      · rw [h.2]
        exact (decide_eq_false hne).symm
      · rw [h.1]
        simp
    · intro h
      refine ⟨?_, ?_⟩
      · have hx := h (σ (Fin.last m)) (Or.inr rfl)
        simpa using hx
      · have hx := h (σ 0) (Or.inl rfl)
        rw [hx]
        exact decide_eq_false hne
  have hkey := card_filter_agree_mul ({σ 0, σ (Fin.last m)} : Finset (Fin (m + 1)))
    (fun x => decide (x = σ (Fin.last m)))
  rw [hcardD, Fintype.card_fin] at hkey
  rw [hfilter, show (4 : ℕ) = 2 ^ 2 from by decide]
  convert hkey using 2
  simp

/-- **Lemma 10.2.7.** An `(m+1)`-vertex tournament with `P` Hamilton paths extends by one
vertex to a tournament with at least `P / 4` Hamilton cycles — stated as `P ≤ 4 · #cycles`.

The notes orient the new vertex's edges uniformly at random: each Hamilton path closes up
with probability `1/4`, distinct paths give distinct cycles, and some orientation attains the
mean. Here the mean is taken by summing over all `2^{m+1}` orientations
(`PMC.card_closingOrients_mul` counts the good ones for each path) and comparing with the
largest term. -/
theorem exists_orientation_hamiltonPaths_le_hamCycles {m : ℕ} (hm : 1 ≤ m)
    (t : Sym2 (Fin (m + 1)) → Bool) :
    ∃ o : Fin (m + 1) → Bool, #(hamiltonPaths t) ≤ 4 * #(hamCycles (extendT t o)) := by
  classical
  set P := #(hamiltonPaths t) with hP
  -- for each orientation, the paths it closes inject into the cycles
  have hinj : ∀ o : Fin (m + 1) → Bool,
      #((hamiltonPaths t).filter fun σ => o (σ (Fin.last m)) = true ∧ o (σ 0) = false)
        ≤ #(hamCycles (extendT t o)) := by
    intro o
    refine Finset.card_le_card_of_injOn cycleOf (fun σ hσ => ?_) (fun σ _ τ _ h => cycleOf_injOn h)
    rw [mem_coe, mem_filter] at hσ
    exact cycleOf_mem_hamCycles t o hσ.1 hσ.2.1 hσ.2.2
  -- double counting: orientation-path pairs
  have hswap : ∑ o : Fin (m + 1) → Bool,
        #((hamiltonPaths t).filter fun σ => o (σ (Fin.last m)) = true ∧ o (σ 0) = false)
      = ∑ σ ∈ hamiltonPaths t, #(closingOrients σ) := by
    simp only [Finset.card_filter, closingOrients]
    rw [Finset.sum_comm]
  have hsum : 4 * ∑ o : Fin (m + 1) → Bool,
      #((hamiltonPaths t).filter fun σ => o (σ (Fin.last m)) = true ∧ o (σ 0) = false)
      = P * 2 ^ (m + 1) := by
    rw [hswap, Finset.mul_sum, hP]
    calc ∑ σ ∈ hamiltonPaths t, 4 * #(closingOrients σ)
        = ∑ _σ ∈ hamiltonPaths t, 2 ^ (m + 1) :=
          Finset.sum_congr rfl fun σ _ =>
            (mul_comm 4 _).trans (card_closingOrients_mul hm σ)
      _ = #(hamiltonPaths t) * 2 ^ (m + 1) := by
          rw [Finset.sum_const, smul_eq_mul]
  -- some orientation is at least as good as the average
  obtain ⟨o₀, -, hmax⟩ := Finset.exists_max_image (univ : Finset (Fin (m + 1) → Bool))
    (fun o => #(hamCycles (extendT t o))) ⟨fun _ => true, mem_univ _⟩
  have hle : ∑ o : Fin (m + 1) → Bool,
        #((hamiltonPaths t).filter fun σ => o (σ (Fin.last m)) = true ∧ o (σ 0) = false)
      ≤ 2 ^ (m + 1) * #(hamCycles (extendT t o₀)) := by
    calc ∑ o : Fin (m + 1) → Bool,
          #((hamiltonPaths t).filter fun σ => o (σ (Fin.last m)) = true ∧ o (σ 0) = false)
        ≤ ∑ o : Fin (m + 1) → Bool, #(hamCycles (extendT t o₀)) :=
          Finset.sum_le_sum fun o _ => le_trans (hinj o) (hmax o (mem_univ o))
      _ = 2 ^ (m + 1) * #(hamCycles (extendT t o₀)) := by
          rw [Finset.sum_const, smul_eq_mul, card_univ, Fintype.card_fun, Fintype.card_bool,
            Fintype.card_fin]
  refine ⟨o₀, ?_⟩
  have hfinal : P * 2 ^ (m + 1) ≤ 4 * #(hamCycles (extendT t o₀)) * 2 ^ (m + 1) := by
    calc P * 2 ^ (m + 1)
        = 4 * ∑ o : Fin (m + 1) → Bool,
            #((hamiltonPaths t).filter fun σ => o (σ (Fin.last m)) = true ∧ o (σ 0) = false) :=
          hsum.symm
      _ ≤ 4 * (2 ^ (m + 1) * #(hamCycles (extendT t o₀))) := by
          exact Nat.mul_le_mul_left 4 hle
      _ = 4 * #(hamCycles (extendT t o₀)) * 2 ^ (m + 1) := by ring
  exact Nat.le_of_mul_le_mul_right hfinal Nat.one_le_two_pow

/-- **Theorem 10.2.4, lower bound.** Some `(m+2)`-vertex tournament has at least
`(m+1)! / (4 · 2^m)` Hamilton cycles.

Szele's theorem (`PMC.exists_tournament_factorial_le_hamiltonPaths`) supplies a tournament
with many Hamilton paths, and Lemma 10.2.7 converts them into cycles. The notes' asymptotic
form is `n!/2^{n-1}` cycles up to a constant; this is that statement with the constant
explicit and no division. -/
theorem exists_tournament_factorial_le_hamCycles {m : ℕ} (hm : 1 ≤ m) :
    ∃ t' : Sym2 (Fin (m + 2)) → Bool,
      Nat.factorial (m + 1) ≤ 4 * #(hamCycles t') * 2 ^ m := by
  obtain ⟨t, ht⟩ := exists_tournament_factorial_le_hamiltonPaths (m + 1)
  obtain ⟨o, ho⟩ := exists_orientation_hamiltonPaths_le_hamCycles hm t
  refine ⟨extendT t o, ?_⟩
  calc Nat.factorial (m + 1) ≤ #(hamiltonPaths t) * 2 ^ (m + 1 - 1) := ht
    _ = #(hamiltonPaths t) * 2 ^ m := by norm_num
    _ ≤ 4 * #(hamCycles (extendT t o)) * 2 ^ m := Nat.mul_le_mul_right _ ho

end HamCycles

end PMC
