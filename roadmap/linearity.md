# Chapter 2 — Linearity of Expectations

Phase 1 covered §2.3, which is complete. Phase 2 opens the rest of the chapter. Each
section below records what is formalized, what route to take when the book's own proof
does not transfer, and — for §2.6 — why the node is deferred outright.

Definitions these sections need are absent from Mathlib and are authored at the
centralized layer in `ProbMethods/Basic.lean` before any task references them.

## Turán's theorem and independent sets (§2.3)

Mathlib has Turán's theorem in structural form
(`SimpleGraph.isTuranMaximal_iff_nonempty_iso_turanGraph`): the extremal `K_{r+1}`-free
graphs are the Turán graphs. It does not have the edge-count bound the notes derive, nor
Caro–Wei. Both are nodes here.

### caro_wei
`PMC.exists_isIndepSet_caro_wei` — Theorem 2.3.2 (Caro 1979, Wei 1981).

Every graph has an independent set of size at least `∑ v, 1 / (d v + 1)`.

Zhao's proof: take a uniformly random ordering of the vertices and keep every vertex that
precedes all of its neighbours. The kept set is independent, and `v` is kept exactly when
it comes first among `{v} ∪ N(v)`, which happens with probability `1 / (d v + 1)`; so the
expected size is `∑ v, 1 / (d v + 1)` and some ordering does at least as well.

Remark 2.3.4 gives a derandomization that is likely the easier Lean route: repeatedly
remove a vertex of smallest degree together with its neighbours, charging weight
`1 / (d v + 1)` to each vertex removed. Total weight removed per step is at most 1, so the
process runs for at least `∑ v, 1 / (d v + 1)` steps, each contributing one vertex to an
independent set. Either proof is acceptable.

### caro_wei_clique
`PMC.exists_isClique_caro_wei` — Corollary 2.3.5.

Every `n`-vertex graph has a clique of size at least `∑ v, 1 / (n - d v)`. Apply
`caro_wei` to the complement, where `v` has degree `n - 1 - d v`, so
`1 / (deg_{Gᶜ} v + 1) = 1 / (n - d v)`.

### turan_edges
`PMC.card_edgeFinset_le_of_cliqueFree` — Theorem 2.3.6 (Turán 1941).

An `n`-vertex `K_{r+1}`-free graph has at most `(1 - 1/r) · n² / 2` edges.

Zhao's proof: `K_{r+1}`-freeness bounds the clique from `caro_wei_clique` by `r`, so
`r ≥ ∑_v 1/(n - d_v) ≥ n / (n - (1/n) ∑_v d_v) = n / (n - 2m/n)` by the AM–HM inequality
(equivalently, convexity of `x ↦ 1/x`). Rearranging gives `m ≤ (1 - 1/r) n² / 2`.

This is the one node in phase 1 with a real analytic step. Do not hand-roll the AM–HM
inequality: Mathlib has it as `Finset.sq_sum_div_le_sum_sq_div` (Sedrakyan's lemma, aka
Titu's or Engel's form, in `Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean`), which
gives `∑ (f i)^2 / g i ≥ (∑ f i)^2 / ∑ g i`. Taking `f ≡ 1` and `g v = n - d v` is exactly
the step needed. `Finset.sum_degrees_eq_twice_card_edges` supplies `∑ v, d v = 2 * m`.

## Hamiltonian paths in tournaments (§2.1)

`PMC.beats` and `PMC.hamiltonPaths` (`ProbMethods/Basic.lean`) encode a tournament on
`Fin n` as a function `t : Sym2 (Fin n) → Bool`, read against the linear order on `Fin n`:
on the edge `s(a, b)` with `a < b`, `true` means `a` beats `b`. Diagonal values `t s(a, a)`
are never consulted, so every tournament is represented equally often and the averaging
argument can range over all `2 ^ Fintype.card (Sym2 (Fin n))` functions. This is the same
larger-uniform-space device the Chapter 1 counting proofs converged on independently.

A Hamilton path is an ordering `σ : Equiv.Perm (Fin n)` of the vertices, `σ i` being the
vertex in position `i`, with every consecutive pair directed forwards. Consecutive
positions are picked out by `(j : ℕ) = (i : ℕ) + 1` over a pair `i j : Fin n`, rather than
by indexing over `Fin (n - 1)`, so the definition carries no truncated subtraction.

The definitions were checked against small cases before being committed: over all `64`
tournaments on `3` vertices the Hamilton-path counts total `96 = 3! * 2 ^ 4`, over all `8`
tournaments on `2` vertices they total `8 = 2! * 2 ^ 2`, and `beats t a b = !beats t b a`
evaluates to `true` for every `t` and every `a ≠ b` on `Fin 3`. Those totals are exactly
the identity the counting proof needs.

### szele
`PMC.exists_tournament_factorial_le_hamiltonPaths` — Theorem 2.1.2 (Szele 1943), per the
notes the first use of the probabilistic method.

Some tournament on `n` vertices has at least `n! / 2 ^ (n - 1)` Hamilton paths, stated
multiplicatively as `n ! ≤ #(hamiltonPaths t) * 2 ^ (n - 1)` to avoid division and
truncated subtraction.

Zhao's proof orients each edge independently and uniformly. A fixed ordering is a Hamilton
path with probability `2 ^ (1 - n)` because it constrains `n - 1` distinct edges, so the
expectation is `n! * 2 ^ (1 - n)` and some tournament meets it. In counting form: summing
`#(hamiltonPaths t)` over all `t` and exchanging the order of summation gives
`n! * 2 ^ (M - (n - 1))` with `M = Fintype.card (Sym2 (Fin n))`, and the maximum is at
least the mean. That the `n - 1` consecutive pairs are *distinct* edges is the one step
worth care — it holds because a path visits distinct vertices.

The minimisation half of Question 2.1.1 is not a node: the notes leave it as an exercise
and it is not a probabilistic argument.

## Sum-free subsets (§2.2)

Theorem 2.2.1 (Erdős 1965): every set of `n` nonzero integers contains a sum-free subset
of size at least `n / 3`.

**The book's proof does not transfer.** It draws `θ` uniformly from `[0, 1]` and takes
`A_θ = {a ∈ A : {aθ} ∈ (1/3, 2/3)}`, then computes `E|A_θ| = n/3`. That is an average over
a continuum against Lebesgue measure — outside this project's counting convention, and it
would drag `MeasureTheory` into Chapter 2 for a single result.

**Take the discrete route instead** (the Alon–Spencer version). Choose a prime
`p ≡ 2 (mod 3)` with `p > 2 * max |a|`, write `p = 3k + 2`, and let
`M = {k+1, …, 2k+1} ⊆ ZMod p`, which is sum-free. For `θ ∈ {1, …, p-1}` put
`A_θ = {a ∈ A : (a * θ : ZMod p) ∈ M}`. Each `A_θ` is sum-free *as a set of integers*,
because `a + b = c` over `ℤ` forces `aθ + bθ = cθ` in `ZMod p`. Since `a ≢ 0`, the map
`θ ↦ aθ` permutes the nonzero residues, so each `a` lies in `A_θ` for exactly
`#M = k + 1` of the `p - 1` choices. Hence `∑_θ #A_θ = n(k+1)` and some `θ` achieves
`#A_θ ≥ n(k+1)/(3k+1) > n/3`.

Prime selection is available rather than something to build: Dirichlet's theorem is in
Mathlib as `Nat.forall_exists_prime_gt_and_eq_mod (ha : IsUnit a) (n : ℕ) : ∃ p > n,
p.Prime ∧ (p : ZMod q) = a`, in `Mathlib/NumberTheory/LSeries/PrimesInAP.lean`. Take
`q = 3` and `a = 2`.

### sumfree
`PMC.exists_sumFree_subset` — Theorem 2.2.1. Stated as `#A ≤ 3 * #B` so the claim stays in
`ℕ` with no division. `PMC.SumFree` is in `ProbMethods/Basic.lean`, defined over any `Add`
structure as `∀ a ∈ A, ∀ b ∈ A, a + b ∉ A`.

The definition was checked before committing: `{1}`, `{3,4,5}` and `{1,3,5,7}` evaluate
sum-free, while `{1,2}`, `{1,2,3}` and `{0,5}` do not — the last because `5 + 0 = 5`, which
is why the theorem needs `0 ∉ A`.

## Sampling (§2.4)

Proposition 2.4.4: every tetrahedron-free 3-graph on `n ≥ 4` vertices has at most
`(7/10) * C(n, 3)` edges.

The averaging half is routine — edge density is preserved by averaging over 5-subsets. The
other half is a finite case check: every tetrahedron-free 3-graph on `5` vertices has at
most `7` of its `10` triples. That is a search over `2 ^ 10 = 1024` hypergraphs, which
`decide` can in principle do, but kernel reduction at that size is where the node will
live or die. Note also that `verify-decide-instance` blocks new `Decidable` instances, so
whatever is written must ride on instances Mathlib already provides.

### sampling_tetrahedron
`PMC.card_le_of_not_hasTetrahedron`, stated as `10 * #H ≤ 7 * n.choose 3` over `ℕ`.

**The notes are off by one here, and the statement corrects them.** Proposition 2.4.4 is
printed for `n ≥ 4`, but it is false at `n = 4`: brute force over all `2 ^ 4` families of
triples on four vertices gives a maximum tetrahedron-free size of **3** — drop any single
triple and no tetrahedron survives — while `(7/10) * C(4,3) = 2.8`. Our statement requires
`5 ≤ n`, which is also what the argument needs, since it samples five vertices. Worth
reporting upstream via the errata form in the notes' preface.

The base case is tight and was computed exhaustively: on five vertices the maximum
tetrahedron-free 3-graph has exactly **7** of the `10` triples, which is where `7/10` comes
from.

**`decide` does not work on the base case, and there is no need for it.** Two things were
measured. First, the base case cannot be quantified over the type `Finset (Finset (Fin 5))`
at all — that is `2 ^ 32` elements. Restricting to `(powersetCard 3 univ).powerset`, the
`1024` families of triples, makes it finite enough to state, but `decide` still exhausts
the default heartbeat budget and had not finished at twenty times that budget. Even if it
elaborated, the kernel would have to replay it in CI.

**Use the counting argument instead — it is three lines of mathematics.** Let `M` be the
triples *not* in `H`. Every one of the `C(5,4) = 5` four-subsets must miss at least one of
its triples, or it would be a tetrahedron; and each triple lies in exactly `2` four-subsets
(pick the two remaining vertices). So `2 * #M ≥ 5`, hence `#M ≥ 3`, hence `#H ≤ 7`. This
was checked against the brute-force extremal number and is tight.

The sampling step is then a double count resting on the identity
`C(n,3) * C(n-3,2) = 10 * C(n,5)` (verified for `n = 5..11`): summing the triples of `H`
inside each 5-subset gives `#H * C(n-3,2)` on one side and at most `7 * C(n,5)` on the
other.

### Proposition 2.4.2, the four-vertex version — proved

`PMC.card_le_of_not_hasTetrahedron_four`: `4 #H ≤ 3 C(n,3)` for `n ≥ 4`. The same double
count as 2.4.4 with four vertices in place of five, and here the base case *is* the
hypothesis — a `4`-set carrying all four of its triples is a tetrahedron — so no case check is
needed. Worth having next to 2.4.4 because the pair shows exactly what sampling one more
vertex buys (`3/4 → 7/10`) and what it costs (a base case, which is also where the notes' own
`n ≥ 4` slips to `n ≥ 5`).

## Unbalancing lights (§2.5)

Theorem 2.5.1 is asymptotic — `(sqrt(2/π) + o(1)) * n^(3/2)` — so by the roadmap's
convention it is not published in that form. **An explicit-constant version is available,
and is what we will state.** The notes give the exact expectation in passing:
`E|S_n| = n * 2^(1-n) * C(n-1, ⌊(n-1)/2⌋)` for `S_n` a sum of `n` independent uniform
`±1`. Summing over the `n` rows gives

    ∃ x y ∈ {±1}^n,  ∑_{i,j} a_ij x_i y_j  ≥  n^2 * C(n-1, ⌊(n-1)/2⌋) / 2^(n-1),

which is the book's bound with the central limit theorem removed — the CLT is used only to
turn that closed form into `sqrt(2/π) * n^(3/2)`. Stating it this way keeps the node in
Chapter 2 rather than deferring it behind Chapter 9's machinery.

Theorem 2.5.2 **was** recorded here as not a node, on the ground that its proof rests on a
compactness argument producing an unspecified constant `c_k`, "which is not something a
`prove` task can be checked against". **The constant is `2^{-k}`, and both 2.5.2 and its
Lemma 2.5.3 are now proved** — see below.

### unbalancing_lights
`PMC.exists_signs_two_pow_mul_le` — Theorem 2.5.1, explicit form. Written multiplicatively
over `ℤ`:

    (n : ℤ) ^ 2 * C(n-1, ⌊(n-1)/2⌋)  ≤  (∑ i, ∑ j, a i j * x i * y j) * 2 ^ (n - 1)

The bound was checked before committing, since an off-by-one here would make the task
unprovable rather than merely hard. The underlying identity
`∑ over y in {±1}^n of |∑ j, y j| = 2n * C(n-1, ⌊(n-1)/2⌋)` holds for `n = 1..7`, and the
theorem itself was verified **exhaustively over every `±1` matrix** for `n = 1..4`. It is
*tight* at `n = 1` and `n = 2` — the hardest matrix meets the bound exactly — which is the
useful part of the check: it says the constant is not accidentally slack, so a proof that
loses anything will fail.

### poly_cube — Lemma 2.5.3, with `c_k = 2^{-k}`

`PMC.exists_abs_eval_ge` (`ProbMethods/Chapter02/PolyCube.lean`): if `g` has degree at most
`k` in `k` variables and the coefficient of `p₁p₂⋯p_k` is `1`, then `|g(p)| ≥ 2^{-k}` at one
of the `2^k` **corners** of `[0,1]^k`.

The notes' proof is a compactness argument — `M(g) = max_{[0,1]^k}|g|` is continuous and
positive on the compact family of admissible coefficient vectors, hence has a positive minimum
— and yields no value for `c_k`. The explicit proof is a finite difference:

    Δg = ∑_{S ⊆ [k]} (-1)^{k-#S} g(χ_S)

is *exactly* the coefficient of `p₁⋯p_k`, because the kernel `∑_{S ⊇ T} (-1)^{k-#S}` vanishes
unless `T = [k]`, and a monomial of degree `≤ k` in `k` variables whose exponent vector has
full support is `p₁⋯p_k`. So `2^k` numbers sum to `1` and one of them is `≥ 2^{-k}`.

Two consequences worth recording:

* **the coefficient bound `|aᵢ| ≤ 1` in the notes' hypothesis is not needed.** The finite
  difference isolates one coefficient exactly, whatever the others are — `p₁p₂ + 100(p₁²+p₂²)`
  has `Δ = 1` just like `p₁p₂` does.
* the value `2^{-k}` is what makes Theorem 2.5.2 statable at all.

Checked before committing: `Δg = 1` exactly (to the last bit, over ℚ-valued random
coefficients) and `max_corner |g| ≥ 2^{-k}` for `k = 1..6`, 200 random polynomials each.

### unbalanced_hypergraph — Theorem 2.5.2

`PMC.exists_unbalanced_partSet`: for `V = V₁ ∪ ⋯ ∪ V_k` with `#Vᵢ = n` and a red/blue colouring
of the `k`-element subsets in which every transversal edge is blue, some `S ⊆ V` has

    |#{blue edges in S} − #{red edges in S}| ≥ n^k / 2^k.

**`S` can be taken to be a union of whole parts** — a strengthening that comes free, and the
reason the proof needs no polynomial. The notes form the expected imbalance
`f(p₁,…,p_k) = ∑ a_{i…} p_i⋯` and apply Lemma 2.5.3 to it; but 2.5.3's own proof only ever
evaluates at corners, where `pᵢ ∈ {0,1}` and the random set is deterministic. Applying the
same kernel `PMC.sum_sign_subset` one level up, directly to the signed edge count `D(V_S)`,
gives the theorem with the polynomial never formed:

    ∑_S (-1)^{#Sᶜ} D(V_S) = ∑_{e meets every part} sgn(e) = n^k,

the last step because an edge with `#e = k` meeting all `k` parts is a transversal
(`PMC.filter_image_fst_eq_univ`, whose content is that `∑ᵢ #(e ∩ Vᵢ) = k` with all fibres
nonempty forces all fibres to be singletons), and every transversal is blue by hypothesis.

Brute-forced before committing: over **all** `2^{#free edges}` colourings for `k = n = 2`
(worst case `2`, bound `1`) and over 400 random colourings for `(k,n) = (2,3), (3,2), (2,4)`.
At `(2,3)` the worst colouring gives `3` against a bound of `2.25`, so the constant is not
wildly slack.

## Crossing number inequality (§2.6) — DEFERRED

**Not formalizable against the current Mathlib, and not a node in any planned phase.**

The crossing number is defined through *drawings* of a graph in the plane, and the proof of
Theorem 2.6.2 runs through Euler's formula and a count of faces. Mathlib has no planarity
development at all: searching the library for `Planar`, `crossingNumber`, or Euler's
formula turns up nothing but the words "Planar graphs" in one docstring. Formalizing this
node means first building topological graph theory, which is a larger undertaking than the
rest of this book put together.

Recorded here so that a later orchestrator does not rediscover it from scratch. If Mathlib
gains a planarity development, §2.6 becomes a phase of its own.
