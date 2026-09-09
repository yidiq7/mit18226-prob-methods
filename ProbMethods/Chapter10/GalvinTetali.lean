import ProbMethods.Chapter10.KahnZhao

/-!
# §10.4 — Galvin–Tetali: homomorphism counts (Theorem 10.4.14)

Zhao, *Probabilistic Methods in Combinatorics*, Theorem 10.4.14 (Galvin and Tetali 2004):
for an `n`-vertex `d`-regular **bipartite** `G` and any target graph `H`, loops allowed,

    hom(G, H) ≤ hom(K_{d,d}, H)^{n/(2d)}.

Cleared of the root, as `PMC.card_homSetR_pow_le`:

    hom(G, H)^d ≤ hom(K_{d,d}, H)^{#B}.

Two special cases the notes single out: `H` a single edge with one loop counts independent
sets, so this contains the bipartite case of Kahn–Zhao (`PMC.card_indepR_pow_le_of_bipartite`);
`H = K_q` counts proper `q`-colourings.

The notes state the theorem and say only that "the entropy proof of the bipartite case of
Theorem 10.4.12 extends". It does, and the extension is short here because the global part of
that proof was separated out as `PMC.mul_tupleEntropy_univ_le` — Shearer on the side `A`,
chain rule and block subadditivity on the side `B`. All that changes is the per-vertex bound,

    H(X_{N(b)}) + d·H(X_b | X_{N(b)}) ≤ log hom(K_{d,d}, H).

## Where `hom(K_{d,d}, H)` comes from

The notes get this by taking `d` conditionally independent copies of `X_b` given `X_{N(b)}`
and observing that the resulting tuple is a homomorphism from `K_{d,d}`. Here, as in Kahn's
case, it is the Gibbs variational principle instead — and the target constant is not put in
by hand but *computed*:

* given `X_{N(b)} = a`, the value `X_b` must lie in the common neighbourhood of `a`, so
  `H(X_b | X_{N(b)}) ≤ E[log #commonNbhd(X_{N(b)})]` (`PMC.wcondEntropy_le_sum_log_card`);
* `PMC.wentropy_add_wmean_le_log_sum_exp` at the energy `a ↦ d·log #commonNbhd(a)` bounds the
  sum of the two terms by `log ∑_a #commonNbhd(a)^d`;
* and `∑_a #commonNbhd(a)^d` *is* `hom(K_{d,d}, H)` (`PMC.card_kddHom`): a homomorphism of
  `K_{d,d}` is a tuple `a` on one side together with `d` independent choices from the common
  neighbourhood of `a` on the other.

The energy has to be summed over the tuples with *nonempty* common neighbourhood rather than
over all of them: `Real.log 0 = 0` makes `exp (d log 0) = 1` where `#commonNbhd^d = 0`, so
including the degenerate tuples would inflate the partition function. Restricting is free —
an attained tuple always has `X_b` in its common neighbourhood.
-/

open Finset

namespace PMC

section GalvinTetali

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {W : Type*} [Fintype W] [DecidableEq W]

/-- Homomorphisms from the graph `r` to the graph `s`. Both are given as relations, and `s`
is allowed loops — which is what makes `hom(·, H)` count independent sets for a suitable
`H`. -/
def homSetR (r : V → V → Prop) [DecidableRel r] (s : W → W → Prop) [DecidableRel s] :
    Finset (V → W) :=
  (univ : Finset (V → W)).filter fun f => ∀ u v, r u v → s (f u) (f v)

lemma mem_homSetR {r : V → V → Prop} [DecidableRel r] {s : W → W → Prop} [DecidableRel s]
    {f : V → W} : f ∈ homSetR r s ↔ ∀ u v, r u v → s (f u) (f v) := by
  rw [homSetR, mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩

/-- The common neighbourhood in `s` of a tuple of vertices. -/
def commonNbhd (s : W → W → Prop) [DecidableRel s] {d : ℕ} (a : Fin d → W) : Finset W :=
  (univ : Finset W).filter fun y => ∀ i, s (a i) y

lemma mem_commonNbhd {s : W → W → Prop} [DecidableRel s] {d : ℕ} {a : Fin d → W} {y : W} :
    y ∈ commonNbhd s a ↔ ∀ i, s (a i) y := by
  rw [commonNbhd, mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩

/-- Homomorphisms from `K_{d,d}` to `s`, as a pair of `d`-tuples with every cross pair an
edge. -/
def kddHom (s : W → W → Prop) [DecidableRel s] (d : ℕ) :
    Finset ((Fin d → W) × (Fin d → W)) :=
  (univ : Finset ((Fin d → W) × (Fin d → W))).filter fun p => ∀ i j, s (p.1 i) (p.2 j)

/-- **`hom(K_{d,d}, H) = ∑_a #commonNbhd(a)^d`.** Choose the tuple on one side; the other
side is then `d` independent choices from its common neighbourhood. -/
lemma card_kddHom (s : W → W → Prop) [DecidableRel s] (d : ℕ) :
    #(kddHom s d) = ∑ a : Fin d → W, #(commonNbhd s a) ^ d := by
  classical
  rw [kddHom, Finset.card_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.card_filter, show (univ : Finset (Fin d → W)).filter
      (fun b => ∀ i j, s (a i) (b j)) = Fintype.piFinset fun _ : Fin d => commonNbhd s a from ?_,
    Fintype.card_piFinset, Finset.prod_const, card_univ, Fintype.card_fin]
  ext b
  simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, mem_commonNbhd]
  exact ⟨fun h j i => h i j, fun h i j => h j i⟩

@[simp] lemma card_kddHom_zero (s : W → W → Prop) [DecidableRel s] : #(kddHom s 0) = 1 := by
  rw [kddHom, Finset.filter_true_of_mem (fun p _ => by intro i; exact absurd i.2 (by omega)),
    card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, pow_zero, mul_one]


/-! ### The probability space of homomorphisms -/

/-- The uniform space of homomorphisms `G → H`. -/
abbrev HomSpace (r : V → V → Prop) [DecidableRel r] (s : W → W → Prop) [DecidableRel s] :=
  {f : V → W // f ∈ homSetR r s}

variable (r : V → V → Prop) [DecidableRel r] (s : W → W → Prop) [DecidableRel s]

/-- The uniform weight on homomorphisms. -/
noncomputable def homWeight : HomSpace r s → ℝ :=
  fun _ => (1 : ℝ) / Fintype.card (HomSpace r s)

/-- The value tuple of the random homomorphism. -/
def homInd (v : V) (f : HomSpace r s) : W := f.1 v

lemma card_homSpace : Fintype.card (HomSpace r s) = #(homSetR r s) := Fintype.card_coe _

@[simp] lemma homWeight_apply (f : HomSpace r s) :
    homWeight r s f = (1 : ℝ) / Fintype.card (HomSpace r s) := rfl

lemma homWeight_eq :
    homWeight r s = fun _ : HomSpace r s => (1 : ℝ) / Fintype.card (HomSpace r s) := rfl

lemma homWeight_nonneg : ∀ f : HomSpace r s, 0 ≤ homWeight r s f := by
  intro f
  rw [homWeight_apply]
  positivity

lemma card_homSpace_pos (hne : (homSetR r s).Nonempty) : 0 < Fintype.card (HomSpace r s) := by
  rw [card_homSpace]
  exact card_pos.mpr hne

lemma sum_homWeight (hne : (homSetR r s).Nonempty) :
    ∑ f : HomSpace r s, homWeight r s f = 1 := by
  have h : (0 : ℝ) < Fintype.card (HomSpace r s) := by
    exact_mod_cast card_homSpace_pos r s hne
  rw [homWeight_eq, Finset.sum_const, card_univ, nsmul_eq_mul, mul_one_div,
    div_self (ne_of_gt h)]

/-- **The entropy of the value tuple is `log hom(G, H)`**: the tuple *is* the homomorphism. -/
lemma tupleEntropy_homInd_univ (hne : (homSetR r s).Nonempty) :
    tupleEntropy (homWeight r s) (homInd r s) univ = Real.log #(homSetR r s) := by
  have hinj : Function.Injective (masked (homInd r s) (univ : Finset V)) := by
    intro f g h
    refine Subtype.ext (funext fun v => ?_)
    have hv := congrFun h v
    simp only [masked, if_pos (mem_univ v), Option.some.injEq, homInd] at hv
    exact hv
  have hval := wentropy_uniform_of_injective hinj (card_homSpace_pos r s hne)
  rw [show tupleEntropy (homWeight r s) (homInd r s) univ
      = wentropy (homWeight r s) (masked (homInd r s) univ) from rfl, homWeight_eq, hval,
    card_homSpace]

/-! ### The per-vertex bound -/

/-- **The per-vertex inequality of Galvin–Tetali**:

    H(X_{N(b)}) + d·H(X_b | X_{N(b)}) ≤ log hom(K_{d,d}, H).

The value at `b` lies in the common neighbourhood of the values on `N(b)`, and the Gibbs
variational principle at the energy `d·log #commonNbhd` has partition function exactly
`hom(K_{d,d}, H)` (`PMC.card_kddHom`). -/
lemma tupleEntropy_nbrs_add_mul_le_log_kddHom (hsymm : ∀ u v, r u v → r v u)
    (hne : (homSetR r s).Nonempty) (b : V) {d : ℕ} (hd : #(nbrs r b) = d) :
    tupleEntropy (homWeight r s) (homInd r s) (nbrs r b)
      + (d : ℝ) * wcondEntropy (homWeight r s) (masked (homInd r s) (nbrs r b))
          (homInd r s b)
      ≤ Real.log #(kddHom s d) := by
  classical
  obtain ⟨f₀, hf₀⟩ := hne
  have hw := homWeight_nonneg r s
  have hsum := sum_homWeight r s ⟨f₀, hf₀⟩
  have hdnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  -- an enumeration of the neighbourhood
  set ε : ↥(nbrs r b) ≃ Fin d := Finset.equivFinOfCardEq hd with hεdef
  set e : Fin d → V := fun i => (ε.symm i).1 with hedef
  have hemem : ∀ i, e i ∈ nbrs r b := fun i => (ε.symm i).2
  have heε : ∀ (v : V) (hv : v ∈ nbrs r b), e (ε ⟨v, hv⟩) = v := by
    intro v hv
    rw [hedef]
    simp
  -- the neighbourhood tuple, as a function on `Fin d` rather than as a mask
  set Y : HomSpace r s → (Fin d → W) := fun f i => f.1 (e i) with hYdef
  set g : (V → Option W) → (Fin d → W) := fun u i => (u (e i)).getD (f₀ b) with hgdef
  set h : (Fin d → W) → (V → Option W) :=
    fun a v => if hv : v ∈ nbrs r b then some (a (ε ⟨v, hv⟩)) else none with hhdef
  have hgY : ∀ f : HomSpace r s, g (masked (homInd r s) (nbrs r b) f) = Y f := by
    intro f
    funext i
    rw [hgdef, hYdef]
    simp only [masked, if_pos (hemem i), homInd, Option.getD_some]
  have hhY : ∀ f : HomSpace r s, h (Y f) = masked (homInd r s) (nbrs r b) f := by
    intro f
    funext v
    rw [hhdef]
    by_cases hv : v ∈ nbrs r b
    · simp only [dif_pos hv, masked, if_pos hv, homInd, hYdef, heε v hv]
    · simp only [dif_neg hv, masked, if_neg hv]
  have hEnt : wentropy (homWeight r s) Y
      = tupleEntropy (homWeight r s) (homInd r s) (nbrs r b) :=
    (wentropy_congr (homWeight r s) (masked (homInd r s) (nbrs r b)) Y g h
      (fun f => (hgY f).symm) (fun f => (hhY f).symm)).symm
  have hCond : wcondEntropy (homWeight r s) (masked (homInd r s) (nbrs r b)) (homInd r s b)
      = wcondEntropy (homWeight r s) Y (homInd r s b) :=
    wcondEntropy_congr_left hw (masked (homInd r s) (nbrs r b)) Y (homInd r s b) g h hgY hhY
  -- the value at `b` lies in the common neighbourhood of the values on `N(b)`
  have hsupp : ∀ f : HomSpace r s, homInd r s b f ∈ commonNbhd s (Y f) := by
    intro f
    refine mem_commonNbhd.mpr fun i => ?_
    exact mem_homSetR.mp f.2 (e i) b (hsymm b (e i) (mem_nbrs.mp (hemem i)))
  set T : Finset (Fin d → W) := (univ : Finset (Fin d → W)).filter
    fun a => (commonNbhd s a).Nonempty with hTdef
  have hYT : ∀ f : HomSpace r s, Y f ∈ T := fun f =>
    mem_filter.mpr ⟨mem_univ _, ⟨_, hsupp f⟩⟩
  have hcond_le := wcondEntropy_le_sum_log_card hw Y (homInd r s b) (commonNbhd s) hsupp
  have hgibbs := wentropy_add_wmean_le_log_sum_exp hw hsum Y
    (fun a => (d : ℝ) * Real.log #(commonNbhd s a)) hYT
  have hmean : wmean (homWeight r s) (fun f => (d : ℝ) * Real.log #(commonNbhd s (Y f)))
      = (d : ℝ) * ∑ a, wdist (homWeight r s) Y a * Real.log #(commonNbhd s a) := by
    rw [wmean_comp_eq_sum_wdist (homWeight r s) Y
        (fun a => (d : ℝ) * Real.log #(commonNbhd s a)), Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  -- the partition function is `hom(K_{d,d}, H)`
  have hexp : ∑ t ∈ T, Real.exp ((d : ℝ) * Real.log #(commonNbhd s t))
      ≤ (#(kddHom s d) : ℝ) := by
    have hterm : ∀ t ∈ T, Real.exp ((d : ℝ) * Real.log #(commonNbhd s t))
        = (#(commonNbhd s t) : ℝ) ^ d := by
      intro t ht
      have hpos : (0 : ℝ) < #(commonNbhd s t) := by
        rw [hTdef, mem_filter] at ht
        exact_mod_cast card_pos.mpr ht.2
      rw [mul_comm, ← Real.rpow_def_of_pos hpos, Real.rpow_natCast]
    rw [Finset.sum_congr rfl hterm, card_kddHom]
    push_cast
    exact Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun t _ _ => by positivity
  have hTpos : (0 : ℝ) < ∑ t ∈ T, Real.exp ((d : ℝ) * Real.log #(commonNbhd s t)) :=
    Finset.sum_pos (fun t _ => Real.exp_pos _) ⟨Y ⟨f₀, hf₀⟩, hYT ⟨f₀, hf₀⟩⟩
  have hlog := Real.log_le_log hTpos hexp
  rw [hmean] at hgibbs
  have hmul : (d : ℝ) * wcondEntropy (homWeight r s) Y (homInd r s b)
      ≤ (d : ℝ) * ∑ a, wdist (homWeight r s) Y a * Real.log #(commonNbhd s a) :=
    mul_le_mul_of_nonneg_left hcond_le hdnn
  rw [← hEnt, hCond]
  linarith

/-! ### The theorem -/

/-- **Theorem 10.4.14** (Galvin and Tetali 2004). For a `d`-regular graph `r` with
bipartition `V = A ∪ B`, and any target `s` (loops allowed),

    hom(G, H)^d ≤ hom(K_{d,d}, H)^{#B}.

Since `#A = #B = n/2` for a `d`-regular bipartite graph, this is the notes'
`hom(G,H) ≤ hom(K_{d,d},H)^{n/(2d)}` with the root cleared.

`PMC.mul_tupleEntropy_univ_le` is the whole global argument — it is shared verbatim with
Kahn's case — and `PMC.tupleEntropy_nbrs_add_mul_le_log_kddHom` is the per-vertex bound. What
is left here is the bookkeeping: the bipartition hypotheses give the two Shearer inputs
(`N(b) ⊆ A`, and each `a ∈ A` covered by its `d` neighbours), and `log` turns the entropy
inequality back into a statement about natural numbers.

The degenerate cases are real and are handled first: `d = 0` makes both sides `1`; no
homomorphisms makes the left side `0`; and `B = ∅` forces `V = ∅` once `d ≥ 1`, since a
vertex of `A` would have to be covered `d` times by an empty family. -/
theorem card_homSetR_pow_le (hsymm : ∀ u v, r u v → r v u)
    {A B : Finset V} (hdisj : Disjoint A B) (hcover : A ∪ B = univ)
    (hbip : ∀ u v, r u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A))
    {d : ℕ} (hreg : ∀ v, #(nbrs r v) = d) :
    #(homSetR r s) ^ d ≤ #(kddHom s d) ^ #B := by
  classical
  rcases Nat.eq_zero_or_pos d with rfl | hdpos
  · rw [pow_zero, card_kddHom_zero, one_pow]
  rcases Finset.eq_empty_or_nonempty (homSetR r s) with hemp | hne
  · rw [hemp, Finset.card_empty, zero_pow (by omega)]
    exact Nat.zero_le _
  obtain ⟨f₀, hf₀⟩ := hne
  -- the neighbourhood of a vertex of `B` lies in `A`
  have hAS : ∀ b ∈ B, nbrs r b ⊆ A := by
    intro b hb v hv
    rcases hbip b v (mem_nbrs.mp hv) with ⟨hbA, -⟩ | ⟨-, hvA⟩
    · exact absurd hb (Finset.disjoint_left.mp hdisj hbA)
    · exact hvA
  have hcov : ∀ a ∈ A, d ≤ #(B.filter fun b => a ∈ nbrs r b) := by
    intro a ha
    rw [← hreg a]
    refine Finset.card_le_card fun v hv => ?_
    rw [mem_filter]
    refine ⟨?_, mem_nbrs.mpr (hsymm a v (mem_nbrs.mp hv))⟩
    rcases hbip a v (mem_nbrs.mp hv) with ⟨-, hvB⟩ | ⟨haB, -⟩
    · exact hvB
    · exact absurd haB (Finset.disjoint_left.mp hdisj ha)
  rcases Finset.eq_empty_or_nonempty B with hBemp | hBne
  · -- with `B` empty a vertex of `A` could not be covered at all, so `V` is empty
    have hAemp : A = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro a ha
      have := hcov a ha
      rw [hBemp, Finset.filter_empty, Finset.card_empty] at this
      omega
    have hVempty : IsEmpty V := by
      rw [← Finset.univ_eq_empty_iff, ← hcover, hAemp, hBemp, Finset.empty_union]
    have hone : #(homSetR r s) ≤ 1 := by
      have h1 : Fintype.card (V → W) = 1 := by
        rw [Fintype.card_fun, @Fintype.card_eq_zero V _ hVempty, pow_zero]
      calc #(homSetR r s) ≤ Fintype.card (V → W) := by
            rw [← card_univ]
            exact card_le_card (subset_univ _)
        _ = 1 := h1
    rw [hBemp, Finset.card_empty, pow_zero]
    calc #(homSetR r s) ^ d ≤ 1 ^ d := Nat.pow_le_pow_left hone d
      _ = 1 := one_pow d
  obtain ⟨b₀, hb₀⟩ := hBne
  have hw := homWeight_nonneg r s
  have hsum := sum_homWeight r s ⟨f₀, hf₀⟩
  -- `hom(K_{d,d}, H) ≥ 1`: a neighbour `v` of `b₀` gives the edge `s (f₀ v) (f₀ b₀)`, and
  -- the constant tuples at its ends are a homomorphism of `K_{d,d}`
  have hMpos : 0 < #(kddHom s d) := by
    have hnb : (nbrs r b₀).Nonempty := by
      rw [← Finset.card_pos, hreg b₀]
      exact hdpos
    obtain ⟨v, hv⟩ := hnb
    refine card_pos.mpr ⟨(fun _ => f₀ v, fun _ => f₀ b₀), ?_⟩
    rw [kddHom, mem_filter]
    exact ⟨mem_univ _, fun _ _ =>
      mem_homSetR.mp hf₀ v b₀ (hsymm b₀ v (mem_nbrs.mp hv))⟩
  have hkey : (d : ℝ) * Real.log #(homSetR r s) ≤ (#B : ℝ) * Real.log #(kddHom s d) := by
    have hskel := mul_tupleEntropy_univ_le hw hsum (homInd r s) (nbrs r) hdisj hcover hAS d
      hcov (fun b _ => tupleEntropy_nbrs_add_mul_le_log_kddHom r s hsymm ⟨f₀, hf₀⟩ b (hreg b))
    have hlogd : (d : ℝ) * tupleEntropy (homWeight r s) (homInd r s) univ
        = (d : ℝ) * Real.log #(homSetR r s) := by
      rw [tupleEntropy_homInd_univ r s ⟨f₀, hf₀⟩]
    linarith
  -- back to natural numbers
  have hNpos : 0 < #(homSetR r s) := card_pos.mpr ⟨f₀, hf₀⟩
  have hp1 : (0 : ℝ) < ((#(homSetR r s) ^ d : ℕ) : ℝ) := by exact_mod_cast pow_pos hNpos d
  have hp2 : (0 : ℝ) < ((#(kddHom s d) ^ #B : ℕ) : ℝ) := by exact_mod_cast pow_pos hMpos #B
  have hlogs : Real.log ((#(homSetR r s) ^ d : ℕ) : ℝ)
      ≤ Real.log ((#(kddHom s d) ^ #B : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Nat.cast_pow, Real.log_pow, Real.log_pow]
    exact hkey
  have hexp := Real.exp_le_exp.mpr hlogs
  rw [Real.exp_log hp1, Real.exp_log hp2] at hexp
  exact_mod_cast hexp

/-! ### The two special cases the notes name

`hom(G, H)` counts independent sets when `H` is a single edge with a loop at one end, and
proper `q`-colourings when `H = K_q`. -/

/-- The target graph whose homomorphisms are the independent sets: an edge between `false`
and `true` together with a loop at `false`. A map `f : V → Bool` is a homomorphism exactly
when `{v : f v = true}` is independent. -/
def indepTarget (x y : Bool) : Prop := x = false ∨ y = false

instance : DecidableRel indepTarget := fun x y => by
  rw [indepTarget]
  infer_instance

/-- **Homomorphisms into `PMC.indepTarget` are the independent sets.** -/
theorem card_homSetR_indepTarget : #(homSetR r indepTarget) = #(indepR r) := by
  classical
  refine Finset.card_nbij' (fun f => (univ : Finset V).filter fun v => f v = true)
    (fun S => fun v => decide (v ∈ S)) ?_ ?_ ?_ ?_
  · intro f hf
    refine mem_indepR.mpr fun u hu v hv hr => ?_
    rw [mem_filter] at hu hv
    rcases mem_homSetR.mp hf u v hr with h | h
    · rw [hu.2] at h
      exact absurd h (by decide)
    · rw [hv.2] at h
      exact absurd h (by decide)
  · intro S hS
    refine mem_homSetR.mpr fun u v hr => ?_
    by_cases hu : u ∈ S
    · refine Or.inr ?_
      simp only [decide_eq_false_iff_not]
      exact fun hv => mem_indepR.mp hS u hu v hv hr
    · exact Or.inl (by simp [hu])
  · intro f _
    funext v
    simp
  · intro S _
    ext v
    simp

/-- **`hom(K_{d,d}, ·)` at `PMC.indepTarget` is `2^{d+1} - 1`** — that is, `i(K_{d,d})`. The
all-`false` tuple has both values in its common neighbourhood and every other tuple has only
`false`, so the count is `2^d + (2^d - 1)`. -/
theorem card_kddHom_indepTarget (d : ℕ) : #(kddHom indepTarget d) = 2 ^ (d + 1) - 1 := by
  classical
  rw [card_kddHom]
  have hzero : commonNbhd indepTarget (fun _ : Fin d => false) = univ := by
    ext y
    simp [mem_commonNbhd, indepTarget]
  have hother : ∀ a : Fin d → Bool, a ≠ (fun _ => false) →
      commonNbhd indepTarget a = {false} := by
    intro a ha
    obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
    have hai : a i = true := by
      revert hi
      cases a i <;> simp
    ext y
    simp only [mem_commonNbhd, mem_singleton]
    constructor
    · intro h
      have := h i
      rw [indepTarget, hai] at this
      rcases this with h' | h'
      · exact absurd h' (by simp)
      · exact h'
    · intro hy i
      exact Or.inr hy
  rw [← Finset.add_sum_erase _ _ (mem_univ (fun _ : Fin d => false)), hzero, card_univ,
    Fintype.card_bool,
    Finset.sum_congr rfl (fun a ha => by
      rw [hother a (Finset.ne_of_mem_erase ha), Finset.card_singleton, one_pow]),
    Finset.sum_const, Finset.card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, smul_eq_mul, mul_one, pow_succ]
  have h1 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
  omega

/-- Proper `q`-colourings of `r`, as the homomorphisms into `K_q`. -/
def properColorings (q : ℕ) : Finset (V → Fin q) := homSetR r fun x y => x ≠ y

/-- **Theorem 10.4.14 for proper colourings**: `c_q(G)^d ≤ c_q(K_{d,d})^{#B}` for a
`d`-regular bipartite `G`. Theorem 10.4.15 (Sah–Sawhney–Stoner–Zhao 2020) removes the
bipartite hypothesis here; that is a research result the notes state without proof. -/
theorem card_properColorings_pow_le (q : ℕ) (hsymm : ∀ u v, r u v → r v u)
    {A B : Finset V} (hdisj : Disjoint A B) (hcover : A ∪ B = univ)
    (hbip : ∀ u v, r u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A))
    {d : ℕ} (hreg : ∀ v, #(nbrs r v) = d) :
    #(properColorings r q) ^ d ≤ #(kddHom (fun x y : Fin q => x ≠ y) d) ^ #B :=
  card_homSetR_pow_le r _ hsymm hdisj hcover hbip hreg

/-- **Consistency check: Galvin–Tetali contains Kahn's case.** Instantiating Theorem 10.4.14
at `PMC.indepTarget` and rewriting the two counts reproduces the statement of
`PMC.card_indepR_pow_le_of_bipartite` exactly. Kept as an `example` rather than a second
copy of the theorem — its value is that it is kernel-checked, not that it is citable. -/
example (hsymm : ∀ u v, r u v → r v u) {A B : Finset V} (hdisj : Disjoint A B)
    (hcover : A ∪ B = univ)
    (hbip : ∀ u v, r u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A))
    {d : ℕ} (hreg : ∀ v, #(nbrs r v) = d) :
    #(indepR r) ^ d ≤ (2 ^ (d + 1) - 1) ^ #B := by
  have h := card_homSetR_pow_le r indepTarget hsymm hdisj hcover hbip hreg
  rwa [card_homSetR_indepTarget, card_kddHom_indepTarget] at h

end GalvinTetali

end PMC
