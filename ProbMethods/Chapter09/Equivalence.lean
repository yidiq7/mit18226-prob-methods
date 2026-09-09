import ProbMethods.Weighted

/-!
# §9.4 — the two faces of concentration of measure (Theorem 9.4.8)

Zhao, *Probabilistic Methods in Combinatorics*, Theorem 9.4.8: in a probability space with a
metric, two statements are equivalent for given `t, ε ≥ 0`:

* **(a) expansion**: every `A` with `P(A) ≥ 1/2` has `P(Aₜ) ≥ 1 - ε`;
* **(b) concentration of Lipschitz functions**: every `1`-Lipschitz `f` and every `m` with
  `P(f ≤ m) ≥ 1/2` has `P(f > m + t) ≤ ε`.

This is the theorem that lets §9.4 move between isoperimetry and concentration at will — it is
why Harper's inequality (a statement about neighbourhoods of sets) and the bounded-differences
inequality (a statement about functions) are two readings of one phenomenon.

Both directions are three lines once the right object is named, and the objects are the two
canonical ones: `(a) ⟹ (b)` applies expansion to the sublevel set `{f ≤ m}`, whose
`t`-neighbourhood sits inside `{f ≤ m + t}` because `f` is `1`-Lipschitz; `(b) ⟹ (a)` applies
concentration to `x ↦ dist(x, A)`, which is `1`-Lipschitz with `{dist(·,A) ≤ 0} ⊇ A`.

## The hypotheses on the distance

Only symmetry and the triangle inequality are used, and nothing requires `d x y = 0 → x = y`.
So the theorem applies verbatim to the Hamming distance of §9.4's cube
(`PMC.hamDist`) and to any pseudometric.
-/

open Finset

namespace PMC

section Equivalence

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The `t`-neighbourhood of a set. -/
noncomputable def nbhd (d : Ω → Ω → ℝ) (t : ℝ) (A : Finset Ω) : Finset Ω :=
  (univ : Finset Ω).filter fun x => ∃ a ∈ A, d x a ≤ t

lemma mem_nbhd {d : Ω → Ω → ℝ} {t : ℝ} {A : Finset Ω} {x : Ω} :
    x ∈ nbhd d t A ↔ ∃ a ∈ A, d x a ≤ t := by
  rw [nbhd, mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩

/-- `f` is `1`-Lipschitz for `d`. -/
def LipOne (d : Ω → Ω → ℝ) (f : Ω → ℝ) : Prop := ∀ x y, f x - f y ≤ d x y

/-- The distance from a point to a nonempty set. -/
noncomputable def distToSetM (d : Ω → Ω → ℝ) (A : Finset Ω) (hA : A.Nonempty) (x : Ω) : ℝ :=
  A.inf' hA fun a => d x a

lemma distToSetM_le {d : Ω → Ω → ℝ} {A : Finset Ω} (hA : A.Nonempty) {x a : Ω} (ha : a ∈ A) :
    distToSetM d A hA x ≤ d x a := Finset.inf'_le _ ha

lemma le_distToSetM {d : Ω → Ω → ℝ} {A : Finset Ω} (hA : A.Nonempty) {x : Ω} {c : ℝ}
    (h : ∀ a ∈ A, c ≤ d x a) : c ≤ distToSetM d A hA x := Finset.le_inf' hA _ h

/-- The distance to a set is `1`-Lipschitz — the triangle inequality, taken at the nearest
point. -/
lemma lipOne_distToSetM {d : Ω → Ω → ℝ} (hsymm : ∀ x y, d x y = d y x)
    (htri : ∀ x y z, d x z ≤ d x y + d y z) {A : Finset Ω} (hA : A.Nonempty) :
    LipOne d (distToSetM d A hA) := by
  intro x y
  obtain ⟨a, ha, hay⟩ := Finset.exists_mem_eq_inf' hA fun a => d y a
  have hx : distToSetM d A hA x ≤ d x a := distToSetM_le hA ha
  have hy : distToSetM d A hA y = d y a := hay
  have := htri x y a
  rw [hy]
  linarith

/-- **Theorem 9.4.8, (a) ⟹ (b).** Expansion gives concentration of Lipschitz functions:
apply it to the sublevel set `{f ≤ m}`, whose `t`-neighbourhood lies inside `{f ≤ m + t}`. -/
theorem concentration_of_expansion {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω = 1)
    (d : Ω → Ω → ℝ) {t ε : ℝ}
    (hexp : ∀ A : Finset Ω, 1 / 2 ≤ wprob w A → 1 - ε ≤ wprob w (nbhd d t A))
    (f : Ω → ℝ) (hf : LipOne d f) (m : ℝ)
    (hm : 1 / 2 ≤ wprob w ((univ : Finset Ω).filter fun x => f x ≤ m)) :
    wprob w ((univ : Finset Ω).filter fun x => m + t < f x) ≤ ε := by
  classical
  set A : Finset Ω := (univ : Finset Ω).filter fun x => f x ≤ m with hA
  have hsub : nbhd d t A ⊆ (univ : Finset Ω).filter fun x => f x ≤ m + t := by
    intro x hx
    rw [mem_nbhd] at hx
    obtain ⟨a, ha, hxa⟩ := hx
    rw [hA, mem_filter] at ha
    rw [mem_filter]
    refine ⟨mem_univ _, ?_⟩
    have := hf x a
    linarith [ha.2]
  have hmono := wprob_mono hw hsub
  have hexpA := hexp A hm
  -- the two filtered sets are complementary
  have hcompl : wprob w ((univ : Finset Ω).filter fun x => f x ≤ m + t)
      + wprob w ((univ : Finset Ω).filter fun x => m + t < f x) = 1 := by
    rw [wprob, wprob]
    have hsplit := Finset.sum_filter_add_sum_filter_not (univ : Finset Ω)
      (fun x => f x ≤ m + t) w
    have hneg : ((univ : Finset Ω).filter fun x => ¬ (f x ≤ m + t))
        = (univ : Finset Ω).filter fun x => m + t < f x := by
      refine Finset.filter_congr fun x _ => ?_
      rw [not_le]
    rw [hneg] at hsplit
    rw [hsplit, hsum]
  linarith

/-- **Theorem 9.4.8, (b) ⟹ (a).** Concentration of Lipschitz functions gives expansion: apply
it to `x ↦ dist(x, A)`, which is `1`-Lipschitz and vanishes on `A`. -/
theorem expansion_of_concentration {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω = 1)
    (d : Ω → Ω → ℝ) (hsymm : ∀ x y, d x y = d y x) (htri : ∀ x y z, d x z ≤ d x y + d y z)
    (hzero : ∀ x, d x x = 0) {t ε : ℝ} (ht : 0 ≤ t)
    (hconc : ∀ (f : Ω → ℝ), LipOne d f → ∀ m : ℝ,
      1 / 2 ≤ wprob w ((univ : Finset Ω).filter fun x => f x ≤ m) →
      wprob w ((univ : Finset Ω).filter fun x => m + t < f x) ≤ ε)
    (A : Finset Ω) (hA : 1 / 2 ≤ wprob w A) : 1 - ε ≤ wprob w (nbhd d t A) := by
  classical
  have hAne : A.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty, wprob_empty] at hA
    linarith
  set f : Ω → ℝ := distToSetM d A hAne with hf
  have hlip : LipOne d f := lipOne_distToSetM hsymm htri hAne
  -- `f` vanishes on `A`, so `{f ≤ 0}` has weight at least `1/2`
  have hsubA : A ⊆ (univ : Finset Ω).filter fun x => f x ≤ 0 := by
    intro x hx
    rw [mem_filter]
    refine ⟨mem_univ _, ?_⟩
    rw [hf]
    have := distToSetM_le hAne hx (d := d) (x := x)
    rw [hzero x] at this
    exact this
  have hhalf : 1 / 2 ≤ wprob w ((univ : Finset Ω).filter fun x => f x ≤ 0) :=
    le_trans hA (wprob_mono hw hsubA)
  have hres := hconc f hlip 0 hhalf
  -- `{f ≤ t}` is the neighbourhood, and its complement is `{0 + t < f}`
  have hsub : (univ : Finset Ω).filter (fun x => f x ≤ t) ⊆ nbhd d t A := by
    intro x hx
    rw [mem_filter] at hx
    rw [mem_nbhd]
    obtain ⟨a, ha, hax⟩ := Finset.exists_mem_eq_inf' hAne fun a => d x a
    refine ⟨a, ha, ?_⟩
    rw [hf, distToSetM, hax] at hx
    exact hx.2
  have hmono := wprob_mono hw hsub
  have hcompl : wprob w ((univ : Finset Ω).filter fun x => f x ≤ t)
      + wprob w ((univ : Finset Ω).filter fun x => 0 + t < f x) = 1 := by
    rw [wprob, wprob]
    have hsplit := Finset.sum_filter_add_sum_filter_not (univ : Finset Ω)
      (fun x => f x ≤ t) w
    have hneg : ((univ : Finset Ω).filter fun x => ¬ (f x ≤ t))
        = (univ : Finset Ω).filter fun x => 0 + t < f x := by
      refine Finset.filter_congr fun x _ => ?_
      rw [not_le, zero_add]
    rw [hneg] at hsplit
    rw [hsplit, hsum]
  linarith

end Equivalence

end PMC
