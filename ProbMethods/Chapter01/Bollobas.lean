import ProbMethods.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# §1.2 — Bollobás' two families theorem

Zhao, *Probabilistic Methods in Combinatorics*, Theorems 1.2.4 and 1.2.6.

Sperner's theorem (1.2.2), the LYM inequality (1.2.3) and the Erdős–Ko–Rado theorem
(1.2.9) are already in Mathlib, as `IsAntichain.sperner`,
`Finset.lubell_yamamoto_meshalkin_inequality_sum_inv_choose` and `Finset.erdos_ko_rado`.
-/

open Finset

namespace PMC

section PermCount

variable {γ : Type*} [Fintype γ] [DecidableEq γ]

/-- The permutations of `γ` mapping `P` onto `L`. -/
private def mapsOnto (P L : Finset γ) : Finset (Equiv.Perm γ) :=
  univ.filter fun g => ∀ x, x ∈ P ↔ g x ∈ L

/-- Glue a bijection `P ≃ L` and a bijection of the complements into a permutation. -/
private def permOfPair (P L : Finset γ)
    (uv : ({x : γ // x ∈ P} ≃ {y : γ // y ∈ L}) × ({x : γ // x ∉ P} ≃ {y : γ // y ∉ L})) :
    Equiv.Perm γ :=
  ((Equiv.sumCompl (· ∈ P)).symm.trans (Equiv.sumCongr uv.1 uv.2)).trans (Equiv.sumCompl (· ∈ L))

omit [Fintype γ] in
private lemma permOfPair_apply_mem (P L : Finset γ) (uv) {x : γ} (hx : x ∈ P) :
    permOfPair P L uv x = (uv.1 ⟨x, hx⟩ : γ) := by
  simp [permOfPair, Equiv.sumCompl_symm_apply_of_pos hx]

omit [Fintype γ] in
private lemma permOfPair_apply_not_mem (P L : Finset γ) (uv) {x : γ} (hx : x ∉ P) :
    permOfPair P L uv x = (uv.2 ⟨x, hx⟩ : γ) := by
  simp [permOfPair, Equiv.sumCompl_symm_apply_of_neg hx]

omit [Fintype γ] in
private lemma permOfPair_injective (P L : Finset γ) :
    Function.Injective (permOfPair P L) := by
  rintro ⟨u, v⟩ ⟨u', v'⟩ h
  have h1 : u = u' := by
    ext x
    have := congrArg (fun f => f (x : γ)) h
    simpa [permOfPair_apply_mem P L _ x.2] using this
  have h2 : v = v' := by
    ext x
    have := congrArg (fun f => f (x : γ)) h
    simpa [permOfPair_apply_not_mem P L _ x.2] using this
  simp [h1, h2]

private lemma mapsOnto_eq_image (P L : Finset γ) :
    mapsOnto P L = univ.image (permOfPair P L) := by
  ext g
  simp only [mapsOnto, mem_filter, mem_univ, true_and, mem_image]
  constructor
  · intro hg
    refine ⟨(Equiv.subtypeEquiv g hg, Equiv.subtypeEquiv g fun x => not_congr (hg x)), ?_⟩
    ext x
    by_cases hx : x ∈ P
    · simp [permOfPair_apply_mem P L _ hx]
    · simp [permOfPair_apply_not_mem P L _ hx]
  · rintro ⟨uv, rfl⟩ x
    by_cases hx : x ∈ P
    · simp [permOfPair_apply_mem P L _ hx, hx, (uv.1 ⟨x, hx⟩).2]
    · simp [permOfPair_apply_not_mem P L _ hx, hx, (uv.2 ⟨x, hx⟩).2]

private lemma card_mapsOnto (P L : Finset γ) (h : #P = #L) :
    #(mapsOnto P L) = Nat.factorial (#P) * Nat.factorial (Fintype.card γ - #P) := by
  have hP : Fintype.card {x : γ // x ∈ P} = #P := Fintype.card_coe P
  have hL : Fintype.card {y : γ // y ∈ L} = #P := (Fintype.card_coe L).trans h.symm
  have hPc : Fintype.card {x : γ // x ∉ P} = Fintype.card γ - #P := by
    rw [Fintype.card_subtype_compl, hP]
  have hLc : Fintype.card {y : γ // y ∉ L} = Fintype.card γ - #P := by
    rw [Fintype.card_subtype_compl, hL]
  have e1 : {x : γ // x ∈ P} ≃ {y : γ // y ∈ L} := Fintype.equivOfCardEq (hP.trans hL.symm)
  have e2 : {x : γ // x ∉ P} ≃ {y : γ // y ∉ L} := Fintype.equivOfCardEq (hPc.trans hLc.symm)
  rw [mapsOnto_eq_image, Finset.card_image_of_injective _ (permOfPair_injective P L),
    Finset.card_univ, Fintype.card_prod, Fintype.card_equiv e1, Fintype.card_equiv e2, hP, hPc]

/-- The permutations of `γ` putting all of `P` `w`-below all of its complement. `w` is any
injective ranking of `γ`; the count does not depend on which one. -/
private lemma card_lowPerms (w : γ → ℕ) (hw : Function.Injective w) (P : Finset γ) :
    #(univ.filter fun g : Equiv.Perm γ => ∀ p ∈ P, ∀ q ∈ Pᶜ, w (g p) < w (g q))
      = Nat.factorial (#P) * Nat.factorial (Fintype.card γ - #P) := by
  let _ : LinearOrder γ := LinearOrder.lift' w hw
  have hlt : ∀ x y : γ, x < y ↔ w x < w y := fun _ _ => Iff.rfl
  have hle : ∀ x y : γ, x ≤ y ↔ w x ≤ w y := fun _ _ => Iff.rfl
  set t := Fintype.card γ with ht
  have hat : #P ≤ t := by rw [ht, ← Finset.card_univ]; exact Finset.card_le_univ P
  set ω : Fin t ≃o γ := Fintype.orderIsoFinOfCardEq γ rfl with hω
  set L : Finset γ := univ.image (fun i : Fin (#P) => ω (Fin.castLE hat i)) with hL
  have hLmem : ∀ x : γ, x ∈ L ↔ ((ω.symm x : Fin t) : ℕ) < #P := by
    intro x
    simp only [hL, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      simp
    · intro hx
      refine ⟨⟨((ω.symm x : Fin t) : ℕ), hx⟩, ?_⟩
      have hcast : Fin.castLE hat ⟨((ω.symm x : Fin t) : ℕ), hx⟩ = ω.symm x := by
        apply Fin.ext; simp
      rw [hcast, OrderIso.apply_symm_apply]
  have hLcard : #L = #P := by
    rw [hL, Finset.card_image_of_injective _ ?_, Finset.card_univ, Fintype.card_fin]
    intro i j hij
    exact Fin.castLE_injective hat (ω.injective hij)
  have hLlt : ∀ x ∈ L, ∀ y, y ∉ L → w x < w y := by
    intro x hx y hy
    rw [← hlt]
    have h1 : ((ω.symm x : Fin t) : ℕ) < #P := (hLmem x).mp hx
    have h2 : ¬ (((ω.symm y : Fin t) : ℕ) < #P) := fun h => hy ((hLmem y).mpr h)
    have hfin : ω.symm x < ω.symm y := by rw [Fin.lt_def]; omega
    simpa using (OrderIso.lt_iff_lt ω.symm).mp hfin
  -- the two descriptions of the good permutations agree
  have hiff : ∀ g : Equiv.Perm γ,
      (∀ p ∈ P, ∀ q ∈ Pᶜ, w (g p) < w (g q)) ↔ (∀ x, x ∈ P ↔ g x ∈ L) := by
    intro g
    constructor
    · intro hg
      have hmemimg : ∀ y : γ, y ∈ P.image (g : γ → γ) ↔ g.symm y ∈ P := by
        intro y
        simp only [mem_image]
        constructor
        · rintro ⟨p, hp, rfl⟩; simpa using hp
        · intro h; exact ⟨g.symm y, h, by simp⟩
      have hdown : ∀ y u : γ, u ∈ P.image (g : γ → γ) → y ≤ u → y ∈ P.image (g : γ → γ) := by
        intro y u hu hyu
        by_contra hy
        obtain ⟨p, hp, rfl⟩ := mem_image.mp hu
        have hq : g.symm y ∈ Pᶜ := mem_compl.mpr fun h => hy ((hmemimg y).mpr h)
        have := hg p hp (g.symm y) hq
        rw [Equiv.apply_symm_apply] at this
        exact absurd hyu (not_le.mpr ((hlt _ _).mpr this))
      have hsub : P.image (g : γ → γ) ⊆ L := by
        intro u hu
        by_contra hnu
        have hge : #P ≤ ((ω.symm u : Fin t) : ℕ) := by
          by_contra hc
          exact hnu ((hLmem u).mpr (by omega))
        have h' : ((ω.symm u : Fin t) : ℕ) + 1 ≤ t := (ω.symm u).isLt
        have hbig : ((ω.symm u : Fin t) : ℕ) + 1 ≤ #(P.image (g : γ → γ)) := by
          have : #(univ : Finset (Fin (((ω.symm u : Fin t) : ℕ) + 1))) = _ := Finset.card_univ
          rw [← Fintype.card_fin (((ω.symm u : Fin t) : ℕ) + 1), ← Finset.card_univ]
          refine Finset.card_le_card_of_injOn (fun i => ω (Fin.castLE h' i)) ?_ ?_
          · intro i _
            refine hdown _ u hu ?_
            have : Fin.castLE h' i ≤ ω.symm u := by
              rw [Fin.le_def]; simpa using Nat.lt_succ_iff.mp i.isLt
            simpa using ω.monotone this
          · intro i _ j _ hij
            exact Fin.castLE_injective h' (ω.injective hij)
        rw [Finset.card_image_of_injective _ g.injective] at hbig
        omega
      have himg : P.image (g : γ → γ) = L :=
        Finset.eq_of_subset_of_card_le hsub
          (by rw [hLcard, Finset.card_image_of_injective _ g.injective])
      intro x
      constructor
      · intro hx; rw [← himg]; exact mem_image_of_mem _ hx
      · intro hx
        rw [← himg] at hx
        obtain ⟨p, hp, hgp⟩ := mem_image.mp hx
        exact g.injective hgp ▸ hp
    · intro hg p hp q hq
      refine hLlt _ ((hg p).mp hp) _ ?_
      exact fun h => (mem_compl.mp hq) ((hg q).mpr h)
  have : (univ.filter fun g : Equiv.Perm γ => ∀ p ∈ P, ∀ q ∈ Pᶜ, w (g p) < w (g q))
      = mapsOnto P L := by
    ext g; simp only [mapsOnto, mem_filter, mem_univ, true_and]; exact hiff g
  rw [this, card_mapsOnto P L hLcard.symm]

end PermCount

section LowOrders

/-- The orderings of `Fin n` (as permutations, `σ x` being the position of `x`) that place
every element of `P` before every element of `Q`. -/
private def lowOrders {n : ℕ} (P Q : Finset (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
  univ.filter fun σ => ∀ p ∈ P, ∀ q ∈ Q, σ p < σ q

private lemma mem_lowOrders {n : ℕ} {P Q : Finset (Fin n)} {σ : Equiv.Perm (Fin n)} :
    σ ∈ lowOrders P Q ↔ ∀ p ∈ P, ∀ q ∈ Q, σ p < σ q := by
  simp [lowOrders]

/-- A `1 / C(#P + #Q, #P)` fraction of the orderings of `Fin n` put `P` before `Q`. -/
private lemma card_lowOrders {n : ℕ} (P Q : Finset (Fin n)) (hPQ : Disjoint P Q) :
    #(lowOrders P Q) * (#P + #Q).choose (#P) = Nat.factorial n := by
  have hPT : P ⊆ P ∪ Q := Finset.subset_union_left
  have hQT : Q ⊆ P ∪ Q := Finset.subset_union_right
  have hTcard : #(P ∪ Q) = #P + #Q := Finset.card_union_of_disjoint hPQ
  set Pg : Finset {x : Fin n // x ∈ P ∪ Q} := univ.filter (fun y => (y : Fin n) ∈ P) with hPgdef
  have hPgmem : ∀ y : {x : Fin n // x ∈ P ∪ Q}, y ∈ Pg ↔ (y : Fin n) ∈ P := by
    intro y; simp [hPgdef]
  have hPgcard : #Pg = #P := by
    refine Finset.card_bij (fun (y : {x : Fin n // x ∈ P ∪ Q}) _ => (y : Fin n)) ?_ ?_ ?_
    · intro y hy; exact (hPgmem y).mp hy
    · intro y1 _ y2 _ h; exact Subtype.ext h
    · intro x hx; exact ⟨⟨x, hPT hx⟩, (hPgmem _).mpr hx, rfl⟩
  have hcardg : Fintype.card {x : Fin n // x ∈ P ∪ Q} = #P + #Q := by
    rw [Fintype.card_coe, hTcard]
  have hPgc : ∀ y : {x : Fin n // x ∈ P ∪ Q}, y ∈ Pgᶜ ↔ (y : Fin n) ∈ Q := by
    intro y
    have hy := Finset.mem_union.mp y.2
    rw [Finset.mem_compl, hPgmem]
    constructor
    · intro h; rcases hy with h1 | h1
      · exact absurd h1 h
      · exact h1
    · intro h h'; exact (Finset.disjoint_left.mp hPQ h') h
  -- for each `g`, precomposition is a bijection of the ordering space
  have hfix : ∀ g : Equiv.Perm {x : Fin n // x ∈ P ∪ Q},
      #(univ.filter fun σ : Equiv.Perm (Fin n) =>
          (Equiv.Perm.subtypeCongr g (Equiv.refl _)).trans σ ∈ lowOrders P Q)
        = #(lowOrders P Q) := by
    intro g
    refine Finset.card_equiv (Equiv.mulRight (Equiv.Perm.subtypeCongr g (Equiv.refl _))) ?_
    intro σ
    simp only [mem_filter, mem_univ, true_and, Equiv.coe_mulRight]
    rfl
  -- for each ordering, exactly `#P ! * #Q !` of the shuffles of `P ∪ Q` are good
  have hinner : ∀ σ : Equiv.Perm (Fin n),
      #(univ.filter fun g : Equiv.Perm {x : Fin n // x ∈ P ∪ Q} =>
          (Equiv.Perm.subtypeCongr g (Equiv.refl _)).trans σ ∈ lowOrders P Q)
        = Nat.factorial (#P) * Nat.factorial (#Q) := by
    intro σ
    have hw : Function.Injective
        (fun y : {x : Fin n // x ∈ P ∪ Q} => ((σ (y : Fin n) : Fin n) : ℕ)) := by
      intro y1 y2 h
      exact Subtype.ext (σ.injective (Fin.val_injective h))
    have hEq : (univ.filter fun g : Equiv.Perm {x : Fin n // x ∈ P ∪ Q} =>
          (Equiv.Perm.subtypeCongr g (Equiv.refl _)).trans σ ∈ lowOrders P Q)
        = (univ.filter fun g : Equiv.Perm {x : Fin n // x ∈ P ∪ Q} => ∀ p ∈ Pg, ∀ q ∈ Pgᶜ,
            ((σ ((g p : {x : Fin n // x ∈ P ∪ Q}) : Fin n) : Fin n) : ℕ)
              < ((σ ((g q : {x : Fin n // x ∈ P ∪ Q}) : Fin n) : Fin n) : ℕ)) := by
      ext g
      simp only [mem_filter, mem_univ, true_and, mem_lowOrders, Equiv.trans_apply]
      constructor
      · intro h y hy z hz
        have h1 := h (y : Fin n) ((hPgmem y).mp hy) (z : Fin n) ((hPgc z).mp hz)
        rw [Equiv.Perm.subtypeCongr.left_apply _ _ y.2,
          Equiv.Perm.subtypeCongr.left_apply _ _ z.2] at h1
        simpa [Subtype.coe_eta] using h1
      · intro h p hp q hq
        have h1 := h ⟨p, hPT hp⟩ ((hPgmem _).mpr hp) ⟨q, hQT hq⟩ ((hPgc _).mpr hq)
        rw [Equiv.Perm.subtypeCongr.left_apply _ _ (hPT hp),
          Equiv.Perm.subtypeCongr.left_apply _ _ (hQT hq)]
        exact h1
    have hsub : #P + #Q - #P = #Q := by omega
    rw [hEq, card_lowPerms _ hw Pg, hPgcard, hcardg, hsub]
  -- double count
  have hswap : ∑ _g : Equiv.Perm {x : Fin n // x ∈ P ∪ Q}, #(lowOrders P Q)
      = ∑ _σ : Equiv.Perm (Fin n), Nat.factorial (#P) * Nat.factorial (#Q) := by
    calc ∑ _g : Equiv.Perm {x : Fin n // x ∈ P ∪ Q}, #(lowOrders P Q)
        = ∑ g : Equiv.Perm {x : Fin n // x ∈ P ∪ Q},
            #(univ.filter fun σ : Equiv.Perm (Fin n) =>
              (Equiv.Perm.subtypeCongr g (Equiv.refl _)).trans σ ∈ lowOrders P Q) := by
          exact Finset.sum_congr rfl fun g _ => (hfix g).symm
      _ = ∑ σ : Equiv.Perm (Fin n),
            #(univ.filter fun g : Equiv.Perm {x : Fin n // x ∈ P ∪ Q} =>
              (Equiv.Perm.subtypeCongr g (Equiv.refl _)).trans σ ∈ lowOrders P Q) := by
          simp only [Finset.card_filter]
          exact Finset.sum_comm
      _ = ∑ _σ : Equiv.Perm (Fin n), Nat.factorial (#P) * Nat.factorial (#Q) :=
          Finset.sum_congr rfl fun σ _ => hinner σ
  rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ,
    Fintype.card_perm, Fintype.card_perm, Fintype.card_fin, hcardg, smul_eq_mul,
    smul_eq_mul] at hswap
  -- (#P + #Q)! = C * #P ! * #Q !
  have hchoose : (#P + #Q).choose (#P) * Nat.factorial (#P) * Nat.factorial (#Q)
      = Nat.factorial (#P + #Q) := by
    have := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right (#P) (#Q))
    simpa using this
  have hpos : 0 < Nat.factorial (#P) * Nat.factorial (#Q) :=
    Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc #(lowOrders P Q) * (#P + #Q).choose (#P) * (Nat.factorial (#P) * Nat.factorial (#Q))
      = #(lowOrders P Q) * ((#P + #Q).choose (#P) * Nat.factorial (#P) * Nat.factorial (#Q)) := by
        rw [mul_assoc, mul_assoc]
    _ = #(lowOrders P Q) * Nat.factorial (#P + #Q) := by rw [hchoose]
    _ = Nat.factorial (#P + #Q) * #(lowOrders P Q) := Nat.mul_comm _ _
    _ = Nat.factorial n * (Nat.factorial (#P) * Nat.factorial (#Q)) := hswap

end LowOrders

section Assembly

/-- Bollobás' inequality with the ground set already normalised to `Fin n`. -/
private lemma sum_inv_choose_le_one_fin {n m : ℕ} (P Q : Fin m → Finset (Fin n))
    (hdisj : ∀ i, Disjoint (P i) (Q i))
    (hcross : ∀ i j, i ≠ j → (P i ∩ Q j).Nonempty) :
    ∑ i, (1 : ℝ) / ((#(P i) + #(Q i)).choose (#(P i))) ≤ 1 := by
  have hpd : ∀ i ∈ (univ : Finset (Fin m)), ∀ j ∈ (univ : Finset (Fin m)), i ≠ j →
      Disjoint (lowOrders (P i) (Q i)) (lowOrders (P j) (Q j)) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro σ hi hj
    obtain ⟨x, hx⟩ := hcross i j hij
    obtain ⟨y, hy⟩ := hcross j i (Ne.symm hij)
    rw [Finset.mem_inter] at hx hy
    have h1 := mem_lowOrders.mp hi x hx.1 y hy.2
    have h2 := mem_lowOrders.mp hj y hy.1 x hx.2
    exact absurd h1 (not_lt.mpr h2.le)
  have hsum : ∑ i, #(lowOrders (P i) (Q i)) ≤ Nat.factorial n := by
    rw [← Finset.card_biUnion hpd]
    calc #((univ : Finset (Fin m)).biUnion fun i => lowOrders (P i) (Q i))
        ≤ #(univ : Finset (Equiv.Perm (Fin n))) := Finset.card_le_univ _
      _ = Nat.factorial n := by rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  have hfac : (0 : ℝ) < (Nat.factorial n : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  have hterm : ∀ i : Fin m, (1 : ℝ) / ((#(P i) + #(Q i)).choose (#(P i)))
      = (#(lowOrders (P i) (Q i)) : ℝ) / (Nat.factorial n : ℝ) := by
    intro i
    have hC : (0 : ℝ) < ((#(P i) + #(Q i)).choose (#(P i)) : ℝ) := by
      exact_mod_cast Nat.choose_pos (Nat.le_add_right _ _)
    rw [div_eq_div_iff hC.ne' hfac.ne', one_mul]
    exact_mod_cast (card_lowOrders (P i) (Q i) (hdisj i)).symm
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  rw [← div_eq_mul_inv, div_le_one hfac]
  exact_mod_cast hsum

end Assembly


variable {α : Type*} [DecidableEq α]

/-- **Bollobás' two families theorem** (Zhao, Theorem 1.2.6; Bollobás 1965).

If `A i ∩ B i = ∅` for every `i`, and `A i ∩ B j ≠ ∅` whenever `i ≠ j`, then
`∑ i, (#(A i) + #(B i)).choose (#(A i)) ⁻¹ ≤ 1`.

The book's proof takes a uniformly random ordering of `⋃ i, (A i ∪ B i)` and lets `E i` be
the event that every element of `A i` precedes every element of `B i`, an event of
probability `((#(A i) + #(B i)).choose (#(A i)))⁻¹`. The hypotheses force the `E i` to be
pairwise disjoint, so their probabilities sum to at most `1`. -/
theorem sum_inv_choose_le_one {m : ℕ} (A B : Fin m → Finset α)
    (hdisj : ∀ i, Disjoint (A i) (B i))
    (hcross : ∀ i j, i ≠ j → (A i ∩ B j).Nonempty) :
    ∑ i, (1 : ℝ) / ((#(A i) + #(B i)).choose (#(A i))) ≤ 1 := by
  classical
  set X : Finset α := univ.biUnion (fun i => A i ∪ B i) with hXdef
  have hAX : ∀ i, A i ⊆ X := by
    intro i x hx
    rw [hXdef, Finset.mem_biUnion]
    exact ⟨i, mem_univ i, Finset.mem_union_left _ hx⟩
  have hBX : ∀ i, B i ⊆ X := by
    intro i x hx
    rw [hXdef, Finset.mem_biUnion]
    exact ⟨i, mem_univ i, Finset.mem_union_right _ hx⟩
  obtain ⟨e⟩ : Nonempty ({x : α // x ∈ X} ≃ Fin (#X)) :=
    ⟨Fintype.equivFinOfCardEq (Fintype.card_coe X)⟩
  set F : Finset α → Finset (Fin (#X)) :=
    fun s => ((Finset.filter (fun x : {y : α // y ∈ X} => (x : α) ∈ s) X.attach).image e)
    with hFdef
  have hFiff : ∀ (s : Finset α) (z : Fin (#X)), z ∈ F s ↔ ((e.symm z : α) ∈ s) := by
    intro s z
    rw [hFdef]
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_attach, true_and]
    constructor
    · rintro ⟨y, hy, rfl⟩; simpa using hy
    · intro h; exact ⟨e.symm z, h, by simp⟩
  have hFcard : ∀ s : Finset α, s ⊆ X → #(F s) = #s := by
    intro s hs
    rw [hFdef, Finset.card_image_of_injective _ e.injective]
    refine Finset.card_bij (fun (x : {y : α // y ∈ X}) _ => (x : α)) ?_ ?_ ?_
    · intro x hx; simpa using hx
    · intro x1 _ x2 _ h; exact Subtype.ext h
    · intro y hy; exact ⟨⟨y, hs hy⟩, by simpa using hy, rfl⟩
  have hd : ∀ i, Disjoint (F (A i)) (F (B i)) := by
    intro i
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    exact (Finset.disjoint_left.mp (hdisj i)) ((hFiff _ z).mp hz1) ((hFiff _ z).mp hz2)
  have hc : ∀ i j, i ≠ j → (F (A i) ∩ F (B j)).Nonempty := by
    intro i j hij
    obtain ⟨x, hx⟩ := hcross i j hij
    rw [Finset.mem_inter] at hx
    refine ⟨e ⟨x, hAX i hx.1⟩, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · rw [hFiff]; simpa using hx.1
    · rw [hFiff]; simpa using hx.2
  have hmain := sum_inv_choose_le_one_fin (fun i => F (A i)) (fun i => F (B i)) hd hc
  have hsum : ∑ i : Fin m, (1 : ℝ) / ((#(F (A i)) + #(F (B i))).choose (#(F (A i))))
      = ∑ i : Fin m, (1 : ℝ) / ((#(A i) + #(B i)).choose (#(A i))) :=
    Finset.sum_congr rfl fun i _ => by rw [hFcard _ (hAX i), hFcard _ (hBX i)]
  rw [hsum] at hmain
  exact hmain

/-- **Bollobás' two families theorem, uniform case** (Zhao, Theorem 1.2.4).

If the `A i` are `r`-element sets, the `B i` are `s`-element sets, `A i ∩ B i = ∅` for all
`i` and `A i ∩ B j ≠ ∅` for all `i ≠ j`, then `m ≤ (r + s).choose r`.

This is the special case of `PMC.sum_inv_choose_le_one` in which every summand equals
`((r + s).choose r)⁻¹`. -/
theorem card_le_choose_of_two_families {m r s : ℕ} (A B : Fin m → Finset α)
    (hA : ∀ i, #(A i) = r) (hB : ∀ i, #(B i) = s)
    (hdisj : ∀ i, Disjoint (A i) (B i))
    (hcross : ∀ i j, i ≠ j → (A i ∩ B j).Nonempty) :
    m ≤ (r + s).choose r := by
  sorry

end PMC
