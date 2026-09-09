import ProbMethods.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# §2.5 — Lemma 2.5.3, with an explicit constant

Zhao, *Probabilistic Methods in Combinatorics*, Lemma 2.5.3: if `g(p₁,…,p_k)` has degree `k`,
coefficients of absolute value at most `1`, and the coefficient of `p₁p₂⋯p_k` equal to `1`,
then `|g|` is at least some constant `c_k > 0` somewhere on `[0,1]^k`.

The notes prove this by compactness — `M(g) = max_{[0,1]^k} |g|` is continuous and positive on
the compact set of admissible coefficient vectors, so it has a positive minimum — which gives
no value for `c_k`. **The constant is `2^{-k}`, and the proof is a finite difference.** The
alternating sum of `g` over the `2^k` corners of the cube,

    Δg = ∑_{S ⊆ [k]} (-1)^{k - #S} g(χ_S),

kills every monomial whose exponent vector misses a variable, because the inner sum
`∑_{S ⊇ T} (-1)^{k - #S}` vanishes unless `T = [k]`; and a monomial of degree `≤ k` in `k`
variables that misses no variable is exactly `p₁p₂⋯p_k`. So `Δg` *is* the coefficient of
`p₁⋯p_k`, namely `1`, and `2^k` terms summing to `1` cannot all be smaller than `2^{-k}`.

Two things the explicit form buys:

* the coefficient bound `|aᵢ| ≤ 1` is **not needed** — the finite difference isolates the one
  coefficient exactly, whatever the others are;
* Theorem 2.5.2 becomes statable with a constant (`PMC.exists_unbalanced_set`), which is why
  it had been recorded as out of scope.
-/

open Finset MvPolynomial

namespace PMC

section PolyCube

variable {k : ℕ}

/-- The exponent vector of the monomial `p₁p₂⋯p_k`. -/
def onesExp (k : ℕ) : (Fin k) →₀ ℕ := ⟨univ, fun _ => 1, by simp⟩

@[simp] lemma onesExp_apply (i : Fin k) : onesExp k i = 1 := rfl

@[simp] lemma onesExp_support : (onesExp k).support = univ := rfl

/-- The corner of the cube `[0,1]^k` indexed by `S ⊆ [k]`. -/
def corner (S : Finset (Fin k)) : Fin k → ℝ := fun i => if i ∈ S then 1 else 0

lemma corner_mem_Icc (S : Finset (Fin k)) (i : Fin k) : corner S i ∈ Set.Icc (0 : ℝ) 1 := by
  unfold corner
  split <;> norm_num

/-- A monomial is `1` at the corner `χ_S` when its exponent is supported in `S`, and `0`
otherwise: the missing variable contributes `0 ^ (d i) = 0`. -/
lemma prod_corner_pow (S : Finset (Fin k)) (d : Fin k →₀ ℕ) :
    ∏ i, corner S i ^ d i = if d.support ⊆ S then 1 else 0 := by
  split_ifs with h
  · refine Finset.prod_eq_one fun i _ => ?_
    by_cases hi : i ∈ S
    · simp [corner, hi]
    · have hd : d i = 0 := by
        by_contra hne
        exact hi (h (Finsupp.mem_support_iff.mpr hne))
      simp [corner, hi, hd]
  · obtain ⟨i, hi, hiS⟩ := Finset.not_subset.mp h
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    have hne : d i ≠ 0 := Finsupp.mem_support_iff.mp hi
    simp [corner, hiS, zero_pow hne]

/-- **The inclusion–exclusion kernel.** The signed sum over the corners of the indicator of
`T ⊆ S` vanishes unless `T` is everything: reindexing by the complement turns it into
`∑_{R ⊆ Tᶜ} (-1)^{#R}`. -/
lemma sum_sign_subset (T : Finset (Fin k)) :
    ∑ S : Finset (Fin k), (-1 : ℝ) ^ #(Sᶜ) * (if T ⊆ S then 1 else 0)
      = if T = univ then 1 else 0 := by
  classical
  have hinv : Function.Involutive (fun S : Finset (Fin k) => Sᶜ) := fun S => compl_compl S
  have hstep : ∑ S : Finset (Fin k), (-1 : ℝ) ^ #(Sᶜ) * (if T ⊆ S then 1 else 0)
      = ∑ R : Finset (Fin k), (-1 : ℝ) ^ #R * (if R ⊆ Tᶜ then 1 else 0) := by
    refine Fintype.sum_bijective _ hinv.bijective _ _ fun S => ?_
    simp only [Finset.compl_subset_compl]
  have hfilter : ∑ R : Finset (Fin k), (-1 : ℝ) ^ #R * (if R ⊆ Tᶜ then 1 else 0)
      = ∑ R ∈ (Tᶜ : Finset (Fin k)).powerset, (-1 : ℝ) ^ #R := by
    have hpt : ∀ R : Finset (Fin k), (-1 : ℝ) ^ #R * (if R ⊆ Tᶜ then 1 else 0)
        = if R ∈ (Tᶜ : Finset (Fin k)).powerset then (-1 : ℝ) ^ #R else 0 := by
      intro R
      by_cases h : R ⊆ Tᶜ <;> simp [h, Finset.mem_powerset]
    rw [Finset.sum_congr rfl fun R _ => hpt R, Finset.sum_ite_mem, Finset.univ_inter]
  have hcast : ∑ R ∈ (Tᶜ : Finset (Fin k)).powerset, (-1 : ℝ) ^ #R
      = ((∑ R ∈ (Tᶜ : Finset (Fin k)).powerset, (-1 : ℤ) ^ #R : ℤ) : ℝ) := by
    push_cast
    ring
  rw [hstep, hfilter, hcast, Finset.sum_powerset_neg_one_pow_card]
  by_cases h : T = univ
  · simp [h]
  · have : (Tᶜ : Finset (Fin k)) ≠ ∅ := by
      intro hc
      apply h
      rw [← compl_compl T, hc, Finset.compl_empty]
    simp [h, this]

/-- **The finite difference isolates the coefficient of `p₁⋯p_k`.**

`∑_S (-1)^{#Sᶜ} g(χ_S) = coeff_{p₁⋯p_k} g` for every `g` of degree at most `k`: the kernel
`PMC.sum_sign_subset` keeps only the exponent vectors of full support, and a vector of full
support with `∑ dᵢ ≤ k` in `k` variables is the all-ones vector. -/
theorem sum_sign_eval (g : MvPolynomial (Fin k) ℝ) (hdeg : g.totalDegree ≤ k) :
    ∑ S : Finset (Fin k), (-1 : ℝ) ^ #(Sᶜ) * eval (corner S) g = g.coeff (onesExp k) := by
  classical
  have hev : ∀ S : Finset (Fin k), eval (corner S) g
      = ∑ d ∈ g.support, g.coeff d * (if d.support ⊆ S then 1 else 0) := by
    intro S
    rw [MvPolynomial.eval_eq']
    exact Finset.sum_congr rfl fun d _ => by rw [prod_corner_pow]
  -- an exponent vector of full support and degree at most `k` is all ones
  have hkey : ∀ d ∈ g.support, d.support = univ → d = onesExp k := by
    intro d hd hsupp
    have hsum : (d.sum fun _ e => e) ≤ k := le_trans (MvPolynomial.le_totalDegree hd) hdeg
    have hsum' : ∑ i : Fin k, d i ≤ k := by
      rwa [Finsupp.sum_fintype _ _ (fun _ => rfl)] at hsum
    have hge : ∀ i : Fin k, 1 ≤ d i := by
      intro i
      have hi : i ∈ d.support := by rw [hsupp]; exact mem_univ i
      exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
    have hone : ∑ i : Fin k, 1 ≤ ∑ i : Fin k, d i := Finset.sum_le_sum fun i _ => hge i
    have hcard : ∑ _i : Fin k, 1 = k := by simp
    have heqsum : ∑ i : Fin k, d i = ∑ _i : Fin k, 1 := by omega
    have hall := (Finset.sum_eq_sum_iff_of_le fun i (_ : i ∈ univ) => hge i).mp heqsum.symm
    ext i
    rw [onesExp_apply, ← hall i (mem_univ i)]
  calc ∑ S : Finset (Fin k), (-1 : ℝ) ^ #(Sᶜ) * eval (corner S) g
      = ∑ S : Finset (Fin k), ∑ d ∈ g.support,
          g.coeff d * ((-1 : ℝ) ^ #(Sᶜ) * (if d.support ⊆ S then 1 else 0)) := by
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [hev S, Finset.mul_sum]
        exact Finset.sum_congr rfl fun d _ => by ring
    _ = ∑ d ∈ g.support, g.coeff d * ∑ S : Finset (Fin k),
          ((-1 : ℝ) ^ #(Sᶜ) * (if d.support ⊆ S then 1 else 0)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun d _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ d ∈ g.support, g.coeff d * (if d.support = univ then 1 else 0) :=
        Finset.sum_congr rfl fun d _ => by rw [sum_sign_subset]
    _ = g.coeff (onesExp k) := by
        by_cases hmem : onesExp k ∈ g.support
        · have hsingle : ∀ d ∈ g.support, d ≠ onesExp k →
              g.coeff d * (if d.support = univ then (1 : ℝ) else 0) = 0 := by
            intro d hd hdne
            have hns : d.support ≠ univ := fun h => hdne (hkey d hd h)
            simp [hns]
          rw [Finset.sum_eq_single_of_mem (onesExp k) hmem hsingle]
          simp
        · have hzero : g.coeff (onesExp k) = 0 := MvPolynomial.notMem_support_iff.mp hmem
          rw [hzero]
          refine Finset.sum_eq_zero fun d hd => ?_
          have hns : d.support ≠ univ := by
            intro h
            rw [← hkey d hd h] at hmem
            exact hmem hd
          simp [hns]

/-- **Lemma 2.5.3 with `c_k = 2^{-k}`.**

If `g` has degree at most `k` and the coefficient of `p₁p₂⋯p_k` is `1`, then some *corner* of
the cube already has `|g| ≥ 2^{-k}`. The coefficient bound `|aᵢ| ≤ 1` in the notes' hypothesis
plays no role. -/
theorem exists_abs_eval_ge (g : MvPolynomial (Fin k) ℝ) (hdeg : g.totalDegree ≤ k)
    (hone : g.coeff (onesExp k) = 1) :
    ∃ p : Fin k → ℝ, (∀ i, p i ∈ Set.Icc (0 : ℝ) 1) ∧ (1 : ℝ) / 2 ^ k ≤ |eval p g| := by
  classical
  by_contra hcon
  push_neg at hcon
  have hsmall : ∀ S : Finset (Fin k),
      |(-1 : ℝ) ^ #(Sᶜ) * eval (corner S) g| < 1 / 2 ^ k := by
    intro S
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact hcon (corner S) (corner_mem_Icc S)
  have h1 : |∑ S : Finset (Fin k), (-1 : ℝ) ^ #(Sᶜ) * eval (corner S) g|
      ≤ ∑ S : Finset (Fin k), |(-1 : ℝ) ^ #(Sᶜ) * eval (corner S) g| :=
    Finset.abs_sum_le_sum_abs _ _
  have h2 : ∑ S : Finset (Fin k), |(-1 : ℝ) ^ #(Sᶜ) * eval (corner S) g|
      < ∑ _S : Finset (Fin k), (1 : ℝ) / 2 ^ k :=
    Finset.sum_lt_sum_of_nonempty ⟨∅, mem_univ _⟩ fun S _ => hsmall S
  have h3 : ∑ _S : Finset (Fin k), (1 : ℝ) / 2 ^ k = 1 := by
    rw [Finset.sum_const, card_univ, Fintype.card_finset, Fintype.card_fin, nsmul_eq_mul,
      mul_one_div]
    push_cast
    exact div_self (by positivity)
  rw [sum_sign_eval g hdeg, hone, abs_one] at h1
  rw [h3] at h2
  linarith

/-- **Lemma 2.5.3** as the notes state it: a positive constant `c_k`, uniform over the whole
family of admissible polynomials. It is `2^{-k}`. -/
theorem exists_pos_forall_abs_eval_ge (k : ℕ) :
    ∃ c > 0, ∀ g : MvPolynomial (Fin k) ℝ, g.totalDegree ≤ k → g.coeff (onesExp k) = 1 →
      ∃ p : Fin k → ℝ, (∀ i, p i ∈ Set.Icc (0 : ℝ) 1) ∧ c ≤ |eval p g| :=
  ⟨1 / 2 ^ k, by positivity, fun _ hdeg hone => exists_abs_eval_ge _ hdeg hone⟩

/-! ### §2.5 — Theorem 2.5.2, with the constant `2^{-k}`

The notes' proof includes each vertex of `Vᵢ` with probability `pᵢ`, computes the expected
imbalance as a polynomial `f(p₁,…,p_k)` whose `p₁⋯p_k` coefficient is `n^k`, and then invokes
Lemma 2.5.3 to find a `p` where `|f| ≥ c_k n^k`.

Since Lemma 2.5.3's own proof only ever evaluates at the `2^k` *corners* of the cube, that is
where the choice of `pᵢ` lands here too — and at a corner the "random" set is deterministic:
`pᵢ ∈ {0,1}` means `S` is a union of whole parts. So the polynomial never needs to be formed.
Applying the same kernel `PMC.sum_sign_subset` one level up, directly to the signed edge count
`D(V_S)`, gives Theorem 2.5.2 with `c_k = 2^{-k}` and the extra information that **`S` can be
taken to be a union of parts**.
-/

variable {n : ℕ}

/-- The union of the parts indexed by `S ⊆ [k]`, inside the vertex set `[k] × [n]`. -/
def partSet (S : Finset (Fin k)) (n : ℕ) : Finset (Fin k × Fin n) :=
  univ.filter fun v => v.1 ∈ S

/-- The transversal edge attached to `f : [k] → [n]`: one vertex from each part. -/
def transversal (f : Fin k → Fin n) : Finset (Fin k × Fin n) := univ.image fun i => (i, f i)

lemma mem_partSet {S : Finset (Fin k)} {v : Fin k × Fin n} : v ∈ partSet S n ↔ v.1 ∈ S := by
  simp [partSet]

/-- An edge lies inside a union of parts exactly when the parts it meets are among them. -/
lemma subset_partSet_iff (e : Finset (Fin k × Fin n)) (S : Finset (Fin k)) :
    e ⊆ partSet S n ↔ e.image Prod.fst ⊆ S := by
  constructor
  · intro h i hi
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
    exact mem_partSet.mp (h hv)
  · intro h v hv
    exact mem_partSet.mpr (h (Finset.mem_image_of_mem _ hv))

lemma transversal_injective : Function.Injective (transversal (k := k) (n := n)) := by
  intro f g h
  funext i
  have hi : (i, f i) ∈ transversal g := by
    rw [← h]
    exact Finset.mem_image_of_mem _ (mem_univ i)
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hi
  rw [Prod.mk.injEq] at hj
  obtain ⟨h1, h2⟩ := hj
  subst h1
  exact h2.symm

lemma card_transversal (f : Fin k → Fin n) : #(transversal f) = k := by
  rw [transversal, Finset.card_image_of_injective _ (fun i j hij => (Prod.mk.injEq .. ▸ hij).1),
    card_univ, Fintype.card_fin]

lemma image_fst_transversal (f : Fin k → Fin n) : (transversal f).image Prod.fst = univ := by
  rw [transversal, Finset.image_image]
  exact Finset.image_id

/-- **The `k`-edges meeting every part are exactly the transversals**, and there are `n^k` of
them. `∑ᵢ #(e ∩ Vᵢ) = #e = k` with all `k` fibres nonempty forces every fibre to be a single
vertex. -/
theorem filter_image_fst_eq_univ (k n : ℕ) :
  (((univ : Finset (Fin k × Fin n)).powersetCard k)).filter
      (fun e => e.image Prod.fst = univ)
    = (univ : Finset (Fin k → Fin n)).image transversal := by
  classical
  ext e
  simp only [mem_filter, Finset.mem_powersetCard, Finset.mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨⟨-, hcard⟩, himage⟩
    -- every fibre is a single vertex
    have hsumfib : ∑ i : Fin k, #(e.filter fun v => v.1 = i) = #e :=
      (Finset.card_eq_sum_card_fiberwise fun v _ => mem_univ v.1).symm
    have hge : ∀ i : Fin k, 1 ≤ #(e.filter fun v => v.1 = i) := by
      intro i
      have hi : i ∈ e.image Prod.fst := by rw [himage]; exact mem_univ i
      obtain ⟨v, hv, hvi⟩ := Finset.mem_image.mp hi
      exact Finset.card_pos.mpr ⟨v, mem_filter.mpr ⟨hv, hvi⟩⟩
    have hsum1 : ∑ _i : Fin k, 1 ≤ ∑ i : Fin k, #(e.filter fun v => v.1 = i) :=
      Finset.sum_le_sum fun i _ => hge i
    have hcardk : ∑ _i : Fin k, 1 = k := by simp
    have heqsum : ∑ i : Fin k, #(e.filter fun v => v.1 = i) = ∑ _i : Fin k, 1 := by omega
    have hfib := (Finset.sum_eq_sum_iff_of_le fun i (_ : i ∈ univ) => hge i).mp heqsum.symm
    -- pick the vertex in each fibre
    choose a ha using fun i : Fin k => Finset.card_eq_one.mp (hfib i (mem_univ i)).symm
    have hafst : ∀ i, (a i).1 = i := by
      intro i
      have : a i ∈ e.filter fun v => v.1 = i := by rw [ha i]; exact mem_singleton_self _
      exact (mem_filter.mp this).2
    refine ⟨fun i => (a i).2, ?_⟩
    have hbi : (univ : Finset (Fin k)).biUnion (fun i => e.filter fun v => v.1 = i) = e :=
      Finset.biUnion_filter_eq_of_maps_to fun v _ => mem_univ v.1
    have hsing : (fun i : Fin k => e.filter fun v => v.1 = i) = (fun i : Fin k => {a i}) :=
      funext fun i => ha i
    rw [transversal, ← hbi, hsing, Finset.biUnion_singleton]
    exact Finset.image_congr fun i _ => (Prod.ext_iff.mpr ⟨(hafst i).symm, rfl⟩)
  · rintro ⟨f, rfl⟩
    exact ⟨⟨subset_univ _, card_transversal f⟩, image_fst_transversal f⟩
/-- There are `n^k` transversal edges. -/
theorem card_filter_image_fst_eq_univ (k n : ℕ) :
    #((((univ : Finset (Fin k × Fin n)).powersetCard k)).filter
        (fun e => e.image Prod.fst = univ)) = n ^ k := by
  classical
  rw [filter_image_fst_eq_univ, Finset.card_image_of_injective _ transversal_injective,
    card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- **Theorem 2.5.2** with `c_k = 2^{-k}`.

`V = V₁ ∪ ⋯ ∪ V_k` with `#Vᵢ = n`; the `k`-element subsets of `V` are red/blue coloured, and
every transversal edge (one vertex from each part) is blue. Then some `S ⊆ V` has its red and
blue edge counts differing by at least `n^k/2^k`.

The proof is the finite difference of `PMC.sum_sign_subset` applied to the signed edge count
`D(V_S) = ∑_e sgn(e)·[e ⊆ V_S]`: the kernel keeps exactly the edges meeting every part, i.e.
the `n^k` transversals, all of which are blue, so the `2^k` numbers `D(V_S)` have signed sum
`n^k` and one of them is at least `n^k/2^k` in absolute value. -/
theorem exists_unbalanced_partSet (col : Finset (Fin k × Fin n) → Bool)
    (hcol : ∀ f : Fin k → Fin n, col (transversal f) = true) :
    ∃ S : Finset (Fin k),
      (n : ℝ) ^ k / 2 ^ k
        ≤ |(#((((univ : Finset (Fin k × Fin n)).powersetCard k)).filter
                (fun e => e ⊆ partSet S n ∧ col e)) : ℝ)
            - #((((univ : Finset (Fin k × Fin n)).powersetCard k)).filter
                (fun e => e ⊆ partSet S n ∧ ¬ col e))| := by
  classical
  set E : Finset (Finset (Fin k × Fin n)) := (univ : Finset (Fin k × Fin n)).powersetCard k
    with hE
  set sgn : Finset (Fin k × Fin n) → ℝ := fun e => if col e then 1 else -1 with hsgn
  set D : Finset (Fin k) → ℝ := fun S =>
    (#(E.filter (fun e => e ⊆ partSet S n ∧ col e)) : ℝ)
      - #(E.filter (fun e => e ⊆ partSet S n ∧ ¬ col e)) with hD
  -- (1) the signed count as a sum over edges
  have hDsum : ∀ S : Finset (Fin k),
      D S = ∑ e ∈ E, sgn e * (if e ⊆ partSet S n then 1 else 0) := by
    intro S
    rw [hD]
    simp only [Finset.card_filter]
    push_cast
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases h1 : e ⊆ partSet S n <;> by_cases h2 : col e <;>
      simp [hsgn, h1, h2]
  -- (2) the alternating sum keeps exactly the transversals
  have hkernel : ∑ S : Finset (Fin k), (-1 : ℝ) ^ #(Sᶜ) * D S = (n : ℝ) ^ k := by
    calc ∑ S : Finset (Fin k), (-1 : ℝ) ^ #(Sᶜ) * D S
        = ∑ S : Finset (Fin k), ∑ e ∈ E,
            sgn e * ((-1 : ℝ) ^ #(Sᶜ) * (if e.image Prod.fst ⊆ S then 1 else 0)) := by
          refine Finset.sum_congr rfl fun S _ => ?_
          rw [hDsum S, Finset.mul_sum]
          refine Finset.sum_congr rfl fun e _ => ?_
          simp only [subset_partSet_iff]
          ring
      _ = ∑ e ∈ E, sgn e * ∑ S : Finset (Fin k),
            ((-1 : ℝ) ^ #(Sᶜ) * (if e.image Prod.fst ⊆ S then 1 else 0)) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun e _ => (Finset.mul_sum _ _ _).symm
      _ = ∑ e ∈ E, sgn e * (if e.image Prod.fst = univ then 1 else 0) :=
          Finset.sum_congr rfl fun e _ => by rw [sum_sign_subset]
      _ = ∑ e ∈ E.filter (fun e => e.image Prod.fst = univ), sgn e := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun e _ => ?_
          by_cases h : e.image Prod.fst = univ <;> simp [h]
      _ = (n : ℝ) ^ k := by
          have hall : ∀ e ∈ E.filter (fun e => e.image Prod.fst = univ), sgn e = 1 := by
            intro e he
            rw [hE, filter_image_fst_eq_univ] at he
            obtain ⟨f, -, rfl⟩ := Finset.mem_image.mp he
            simp [hsgn, hcol f]
          rw [Finset.sum_congr rfl hall, Finset.sum_const, nsmul_eq_mul, mul_one]
          rw [hE, card_filter_image_fst_eq_univ k n]
          push_cast
          ring
  -- (3) some corner is large
  by_contra hcon
  push_neg at hcon
  have hsmall : ∀ S : Finset (Fin k), |(-1 : ℝ) ^ #(Sᶜ) * D S| < (n : ℝ) ^ k / 2 ^ k := by
    intro S
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact hcon S
  have h1 : |∑ S : Finset (Fin k), (-1 : ℝ) ^ #(Sᶜ) * D S|
      ≤ ∑ S : Finset (Fin k), |(-1 : ℝ) ^ #(Sᶜ) * D S| := Finset.abs_sum_le_sum_abs _ _
  have h2 : ∑ S : Finset (Fin k), |(-1 : ℝ) ^ #(Sᶜ) * D S|
      < ∑ _S : Finset (Fin k), (n : ℝ) ^ k / 2 ^ k :=
    Finset.sum_lt_sum_of_nonempty ⟨∅, mem_univ _⟩ fun S _ => hsmall S
  have h3 : ∑ _S : Finset (Fin k), (n : ℝ) ^ k / 2 ^ k = (n : ℝ) ^ k := by
    rw [Finset.sum_const, card_univ, Fintype.card_finset, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    rw [mul_comm, div_mul_cancel₀ _ (by positivity : ((2 : ℝ) ^ k) ≠ 0)]
  rw [hkernel] at h1
  rw [h3] at h2
  have habs : |(n : ℝ) ^ k| = (n : ℝ) ^ k := abs_of_nonneg (by positivity)
  rw [habs] at h1
  linarith

end PolyCube


end PMC
