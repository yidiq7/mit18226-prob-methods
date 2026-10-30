import ProbMethods.Chapter01.PropertyB

/-!
# §1.3 — Theorem 1.3.3, the upper bound `m(k) = O(k² 2^k)`

Zhao, *Probabilistic Methods in Combinatorics*, Theorem 1.3.3 (Erdős 1964): there is a
`k`-uniform hypergraph with `O(k² 2^k)` edges that is not 2-colourable — so `m k = O(k² 2^k)`,
where `m k` is the least number of edges of a non-2-colourable `k`-uniform hypergraph.
Together with `PMC.twoColorable_of_card_lt_two_pow` (Theorem 1.3.1, `m k ≥ 2^{k-1}`) and
`PMC.twoColorable_of_card_le` (Theorem 3.5.1, `m k ≳ √(k/log k) 2^k`) this brackets `m k`.

**Stated with an explicit constant**, as the roadmap requires: `2 k² 2^k` edges suffice. The
notes' `O(·)` hides a constant that the proof below pins down, and the arithmetic has slack —
`1.39 k² 2^k` is what the estimates give, so `2 k² 2^k` is comfortable.

## The route

Vertices `[k²]`; choose `m = 2 k² 2^k` edges independently and uniformly among all `k`-subsets,
and show some choice is not 2-colourable. Fix a colouring `c`, and let its larger colour class
have `s ≥ k²/2` vertices.

* **A random `k`-set is monochromatic with probability at least `2^{-k-1}`.** It suffices to
  land inside the larger class:

      C(s,k)/C(k²,k) ≥ ∏_{i<k} (k²/2 - i)/(k² - i) ≥ 2^{-k} ∏_{i<k} (1 - i/(k² - k))
                     ≥ 2^{-k} (1 - k(k-1)/(2(k² - k))) = 2^{-k-1},

  the last equality because `k(k-1)/(2(k²-k)) = 1/2` exactly at `k²` vertices. Only
  `∏(1 - xᵢ) ≥ 1 - ∑ xᵢ` is used, which is Weierstrass and holds in `ℕ`-free form.
* **Union bound over colourings.** For a fixed `c`, the probability that no chosen edge is
  monochromatic is at most `(1 - 2^{-k-1})^m ≤ exp(-m 2^{-k-1})`, and there are `2^{k²}`
  colourings, so the failure probability is at most `exp(k² log 2 - m 2^{-k-1}) < 1` as soon as
  `m > k² log 2 · 2^{k+1}`. At `m = 2 k² 2^k` this needs `2 > 2 log 2 = 1.386`.
* **Duplicates are harmless.** The chosen `k`-sets may coincide; the event "no chosen edge is
  monochromatic under `c`" depends only on the *set* `E` of chosen edges, so the surviving `E`
  is not 2-colourable and has `#E ≤ m`. That is why the conclusion is `≤`, not `=`.

The sample space is the `m`-fold product of the `k`-subsets of `[k²]`, i.e. a `unifProd` on
`Fin m → Finset (Fin (k*k))` restricted to `powersetCard k`; the union bound is
`PMC.wprob_biUnion_le`. Nothing here needs the local lemma or a second moment.
-/

open Finset

namespace PMC

section PropertyBUpper

/-- The Weierstrass product estimate, by induction on the number of factors: with `L = k(k-1)`,
`∏_{i<j} (k² - i) · (2L - j(j-1)) ≤ ∏_{i<j} 2(s - i) · 2L` whenever `2s ≥ k²` and `j ≤ k`. -/
private lemma descFactorial_weierstrass {k s : ℕ} (hk : 2 ≤ k) (hs : k * k ≤ 2 * s) :
    ∀ j ≤ k, ((k * k).descFactorial j : ℤ) * (2 * (k * (k - 1)) - j * (j - 1)) ≤
      2 ^ j * s.descFactorial j * (2 * (k * (k - 1))) := by
  intro j
  induction j with
  | zero =>
    intro _
    simp
  | succ j ih =>
    intro hj
    have hjk : j < k := hj
    have ih := ih hjk.le
    have hk2 : 2 * k ≤ k * k := Nat.mul_le_mul_right k hk
    have hjv : j ≤ k * k := by omega
    have hjs : j ≤ s := by omega
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ]
    push_cast [Nat.cast_sub hjv, Nat.cast_sub hjs]
    have hB0 : (0 : ℤ) ≤ ((k * k).descFactorial j : ℤ) := Int.natCast_nonneg _
    have hS0 : (0 : ℤ) ≤ (s.descFactorial j : ℤ) := Int.natCast_nonneg _
    have hj0 : (0 : ℤ) ≤ j := Int.natCast_nonneg j
    have hjj : (j : ℤ) ≤ j * j := by exact_mod_cast Nat.le_mul_self j
    have hjkZ : (j : ℤ) + 1 ≤ k := by exact_mod_cast hjk
    have hsZ : (k : ℤ) * k ≤ 2 * s := by exact_mod_cast hs
    have hk2Z : 2 * (k : ℤ) ≤ k * k := by exact_mod_cast hk2
    generalize ((k * k).descFactorial j : ℤ) = B at ih hB0 ⊢
    generalize (s.descFactorial j : ℤ) = S at ih hS0 ⊢
    have hL0 : (0 : ℤ) ≤ 2 * ((k : ℤ) * (k - 1)) :=
      Int.mul_nonneg (by omega) (Int.mul_nonneg (by omega) (by omega))
    have hA0 : (0 : ℤ) ≤ 2 ^ j * S * (2 * ((k : ℤ) * (k - 1))) :=
      Int.mul_nonneg (Int.mul_nonneg (Int.pow_nonneg (by omega)) hS0) hL0
    have hfac : (0 : ℤ) ≤ (k : ℤ) * k - 2 * j := by omega
    have hstep : ((k : ℤ) * k - j) * (2 * ((k : ℤ) * (k - 1)) - j * (j - 1) - 2 * j) ≤
        (2 * ((k : ℤ) * (k - 1)) - j * (j - 1)) * ((k : ℤ) * k - 2 * j) := by
      have hd : (0 : ℤ) ≤ j * (2 * ((k : ℤ) - j) + (j * j - j)) :=
        Int.mul_nonneg hj0 (by omega)
      grind
    calc ((k : ℤ) * k - j) * B * (2 * ((k : ℤ) * (k - 1)) - (j + 1) * (j + 1 - 1))
        = B * (((k : ℤ) * k - j) * (2 * ((k : ℤ) * (k - 1)) - j * (j - 1) - 2 * j)) := by grind
      _ ≤ B * ((2 * ((k : ℤ) * (k - 1)) - j * (j - 1)) * ((k : ℤ) * k - 2 * j)) :=
          Int.mul_le_mul_of_nonneg_left hstep hB0
      _ = (B * (2 * ((k : ℤ) * (k - 1)) - j * (j - 1))) * ((k : ℤ) * k - 2 * j) := by grind
      _ ≤ (2 ^ j * S * (2 * ((k : ℤ) * (k - 1)))) * ((k : ℤ) * k - 2 * j) :=
          Int.mul_le_mul_of_nonneg_right ih hfac
      _ ≤ (2 ^ j * S * (2 * ((k : ℤ) * (k - 1)))) * (2 * ((s : ℤ) - j)) :=
          Int.mul_le_mul_of_nonneg_left (by omega) hA0
      _ = 2 ^ (j + 1) * (((s : ℤ) - j) * S) * (2 * ((k : ℤ) * (k - 1))) := by grind

/-- A set of at least half of `k²` vertices contains at least a `2^{-k-1}` fraction of the
`k`-subsets of `[k²]`. -/
private lemma choose_le_choose_mul_two_pow {k s : ℕ} (hk : 2 ≤ k) (hs : k * k ≤ 2 * s) :
    (k * k).choose k ≤ s.choose k * 2 ^ (k + 1) := by
  have h := descFactorial_weierstrass hk hs k le_rfl
  have hL : (0 : ℤ) < (k : ℤ) * (k - 1) := Int.mul_pos (by omega) (by omega)
  have hd : (k * k).descFactorial k ≤ s.descFactorial k * 2 ^ (k + 1) := by
    have h' : ((k * k).descFactorial k : ℤ) ≤ s.descFactorial k * 2 ^ (k + 1) := by
      refine Int.le_of_mul_le_mul_right ?_ hL
      calc ((k * k).descFactorial k : ℤ) * ((k : ℤ) * (k - 1))
          = ((k * k).descFactorial k : ℤ) * (2 * ((k : ℤ) * (k - 1)) - k * (k - 1)) := by grind
        _ ≤ 2 ^ k * s.descFactorial k * (2 * ((k : ℤ) * (k - 1))) := h
        _ = s.descFactorial k * 2 ^ (k + 1) * ((k : ℤ) * (k - 1)) := by grind
    exact_mod_cast h'
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.mul_assoc] at hd
  exact Nat.le_of_mul_le_mul_left hd (Nat.factorial_pos k)

/-- Bernoulli's inequality in the form `x ^ n (x + n) ≤ x (x + 1) ^ n`. -/
private lemma pow_mul_add_le_mul_succ_pow (x n : ℕ) :
    x ^ n * (x + n) ≤ x * (x + 1) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc x ^ (n + 1) * (x + (n + 1))
        ≤ x ^ (n + 1) * (x + (n + 1)) + x ^ n * n := Nat.le_add_right _ _
      _ = (x + 1) * (x ^ n * (x + n)) := by grind
      _ ≤ (x + 1) * (x * (x + 1) ^ n) := Nat.mul_le_mul_left _ ih
      _ = x * (x + 1) ^ (n + 1) := by grind

/-- If `g ≤ (1 - 1/D) N` with `D > 0`, `N > 0` and `v > 0`, then `2 ^ v g ^ (D v) < N ^ (D v)`:
this is `(1 - 1/D) ^ D < 1/2`. -/
private lemma two_pow_mul_pow_lt {g N D v : ℕ} (hN : 0 < N) (hD : 0 < D) (hv : v ≠ 0)
    (hg : g * D + N ≤ N * D) : 2 ^ v * g ^ (D * v) < N ^ (D * v) := by
  obtain ⟨x, rfl⟩ : ∃ x, D = x + 1 := ⟨D - 1, by omega⟩
  have hgx : g * (x + 1) ≤ N * x := by
    rw [Nat.mul_add_one N x] at hg
    omega
  have hbern : 2 * x ^ (x + 1) < (x + 1) ^ (x + 1) := by
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp
    · have h := pow_mul_add_le_mul_succ_pow x (x + 1)
      have hxx : 0 < x ^ (x + 1) := pow_pos hx _
      have heq : x ^ (x + 1) * (x + (x + 1)) = x * (2 * x ^ (x + 1)) + x ^ (x + 1) := by grind
      exact Nat.lt_of_mul_lt_mul_left (a := x) (by omega)
  have hbase : 2 * g ^ (x + 1) < N ^ (x + 1) := by
    have hpow : g ^ (x + 1) * (x + 1) ^ (x + 1) ≤ N ^ (x + 1) * x ^ (x + 1) := by
      rw [← mul_pow, ← mul_pow]
      exact Nat.pow_le_pow_left hgx _
    refine Nat.lt_of_mul_lt_mul_right (a := (x + 1) ^ (x + 1)) ?_
    calc 2 * g ^ (x + 1) * (x + 1) ^ (x + 1)
        = 2 * (g ^ (x + 1) * (x + 1) ^ (x + 1)) := Nat.mul_assoc _ _ _
      _ ≤ 2 * (N ^ (x + 1) * x ^ (x + 1)) := Nat.mul_le_mul_left _ hpow
      _ = N ^ (x + 1) * (2 * x ^ (x + 1)) := by grind
      _ < N ^ (x + 1) * (x + 1) ^ (x + 1) := Nat.mul_lt_mul_of_pos_left hbern (pow_pos hN _)
  calc 2 ^ v * g ^ ((x + 1) * v) = (2 * g ^ (x + 1)) ^ v := by rw [mul_pow, pow_mul]
    _ < (N ^ (x + 1)) ^ v := Nat.pow_lt_pow_left hbase hv
    _ = N ^ ((x + 1) * v) := by rw [pow_mul]

/-- The union bound over a finite family: if each `G c` has `#ι * #(G c) ^ m < #P ^ m`, then
some `m`-tuple from `P` leaves every `G c`. -/
private lemma exists_tuple_forall_exists_notMem {ι α : Type*} [Fintype ι] [Nonempty ι]
    (P : Finset α) (G : ι → Finset α) (m : ℕ)
    (h : ∀ c, Fintype.card ι * #(G c) ^ m < #P ^ m) :
    ∃ f : Fin m → α, (∀ j, f j ∈ P) ∧ ∀ c, ∃ j, f j ∉ G c := by
  classical
  have hlt : #(univ.biUnion fun c => Fintype.piFinset fun _ : Fin m => G c) <
      #(Fintype.piFinset fun _ : Fin m => P) := by
    refine Nat.lt_of_mul_lt_mul_left (a := Fintype.card ι) ?_
    calc Fintype.card ι * #(univ.biUnion fun c => Fintype.piFinset fun _ : Fin m => G c)
        ≤ Fintype.card ι * ∑ c, #(G c) ^ m := by
          refine Nat.mul_le_mul_left _ (card_biUnion_le.trans_eq ?_)
          simp
      _ = ∑ c, Fintype.card ι * #(G c) ^ m := by
          simp only [← smul_eq_mul, sum_nsmul]
      _ < ∑ _c : ι, #P ^ m := sum_lt_sum_of_nonempty univ_nonempty fun c _ => h c
      _ = Fintype.card ι * #(Fintype.piFinset fun _ : Fin m => P) := by
          simp [card_univ]
  obtain ⟨f, hfP, hf⟩ := exists_mem_notMem_of_card_lt_card hlt
  refine ⟨f, Fintype.mem_piFinset.1 hfP, fun c => ?_⟩
  by_contra hc
  exact hf (mem_biUnion.2 ⟨c, mem_univ c, Fintype.mem_piFinset.2 (not_exists_not.1 hc)⟩)

/-- **Theorem 1.3.3** (Erdős 1964) with an explicit constant: for every `k ≥ 2` there is a
`k`-uniform hypergraph on `k²` vertices with at most `2 k² 2^k` edges that is not
2-colourable. Hence `m k ≤ 2 k² 2^k = O(k² 2^k)`. -/
theorem exists_not_twoColorable_card_le {k : ℕ} (hk : 2 ≤ k) :
    ∃ E : Finset (Finset (Fin (k * k))),
      (∀ e ∈ E, #e = k) ∧ #E ≤ 2 * (k * k) * 2 ^ k ∧ ¬ TwoColorable E := by
  classical
  set P : Finset (Finset (Fin (k * k))) := powersetCard k univ with hP
  have hPcard : #P = (k * k).choose k := by simp [hP]
  have hNpos : 0 < #P := by
    rw [hPcard]
    exact Nat.choose_pos (Nat.le_mul_self k)
  have hv : k * k ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  -- `G c` is the family of `k`-sets that are not monochromatic under `c`.
  let G : (Fin (k * k) → Bool) → Finset (Finset (Fin (k * k))) :=
    fun c => {e ∈ P | ∃ u ∈ e, ∃ v ∈ e, c u ≠ c v}
  have hG : ∀ c, #(G c) * 2 ^ (k + 1) + #P ≤ #P * 2 ^ (k + 1) := by
    intro c
    -- The larger colour class holds at least half of the vertices.
    obtain ⟨b, hb⟩ : ∃ b, k * k ≤ 2 * #{x | c x = b} := by
      have htot : #{x | c x = true} + #{x | c x = false} = k * k := by
        simp only [← Bool.not_eq_true, card_filter_add_card_filter_not]
        simp
      by_cases htrue : k * k ≤ 2 * #{x | c x = true}
      · exact ⟨true, htrue⟩
      · exact ⟨false, by omega⟩
    set S : Finset (Fin (k * k)) := {x | c x = b} with hS
    have hmono : powersetCard k S ⊆ P \ G c := by
      intro e he
      obtain ⟨heS, hek⟩ := mem_powersetCard.1 he
      refine mem_sdiff.2 ⟨mem_powersetCard.2 ⟨subset_univ _, hek⟩, fun heG => ?_⟩
      obtain ⟨u, hu, v, hv', huv⟩ := (mem_filter.1 heG).2
      exact huv (((mem_filter.1 (heS hu)).2).trans (mem_filter.1 (heS hv')).2.symm)
    have hlow : (#S).choose k + #(G c) ≤ #P := by
      have hGP : G c ⊆ P := filter_subset _ _
      have h1 := card_le_card hmono
      rw [card_sdiff_of_subset hGP, card_powersetCard] at h1
      have h2 := card_le_card hGP
      omega
    have hch := choose_le_choose_mul_two_pow hk hb
    rw [← hPcard] at hch
    calc #(G c) * 2 ^ (k + 1) + #P
        ≤ #(G c) * 2 ^ (k + 1) + (#S).choose k * 2 ^ (k + 1) := Nat.add_le_add_left hch _
      _ = ((#S).choose k + #(G c)) * 2 ^ (k + 1) := by rw [Nat.add_mul, Nat.add_comm]
      _ ≤ #P * 2 ^ (k + 1) := Nat.mul_le_mul_right _ hlow
  have hcard : Fintype.card (Fin (k * k) → Bool) = 2 ^ (k * k) := by simp
  have hm : 2 * (k * k) * 2 ^ k = 2 ^ (k + 1) * (k * k) := by grind
  obtain ⟨f, hfP, hf⟩ := exists_tuple_forall_exists_notMem P G (2 * (k * k) * 2 ^ k) (fun c => by
    rw [hcard, hm]
    exact two_pow_mul_pow_lt hNpos (pow_pos (by omega) _) hv (hG c))
  refine ⟨univ.image f, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨j, -, rfl⟩ := mem_image.1 he
    exact (mem_powersetCard.1 (hfP j)).2
  · exact card_image_le.trans (by simp)
  · rintro ⟨c, hc⟩
    obtain ⟨j, hj⟩ := hf c
    exact hj (mem_filter.2 ⟨hfP j, hc _ (mem_image_of_mem f (mem_univ j))⟩)

end PropertyBUpper

end PMC
