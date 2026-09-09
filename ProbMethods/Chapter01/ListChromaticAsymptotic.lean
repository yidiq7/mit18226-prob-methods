import ProbMethods.Chapter01.ListChromatic
import ProbMethods.Chapter01.PropertyBUpper
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# §1.4 — Corollary 1.4.4, `ch(K_{n,n}) = (1 + o(1)) log₂ n`

Zhao, *Probabilistic Methods in Combinatorics*, Corollary 1.4.4. The list chromatic number of
`K_{n,n}` is `log₂ n` to leading order. Both bounds are already in this development, and the
corollary is the statement that they meet.

`PMC.listChromaticBipartite n` is the least `k` for which `K_{n,n}` is `k`-choosable; it is
well defined because `K_{n,n}` is `2n`-choosable (give every vertex its own colours), so the
set of admissible `k` is nonempty.

## The route

* **Upper bound, from Theorem 1.4.2** (`PMC.completeBipartiteChoosable_of_lt_two_pow`):
  `n < 2^{k-1}` implies `k`-choosable, so `listChromaticBipartite n ≤ ⌈log₂ n⌉ + 1`.
* **Lower bound, from Theorem 1.4.3 and Theorem 1.3.3.** `PMC.not_completeBipartiteChoosable_of_not_twoColorable`
  turns a non-2-colourable `k`-uniform hypergraph with `n` edges into a failure of
  `k`-choosability. Theorem 1.3.3 (task #56, `PMC.exists_not_twoColorable_card_le`) supplies one
  with at most `2k²2^k` edges, and edges may be *added* to a non-2-colourable hypergraph without
  making it 2-colourable — there are `C(k², k) ≫ 2k²2^k` available `k`-subsets of `[k²]`, so it
  can be padded to exactly `n` edges whenever `n ≥ 2k²2^k`. Hence
  `listChromaticBipartite n ≥ k + 1` for every `k` with `2k²2^k ≤ n`, i.e.
  `≥ log₂ n - 2log₂ k - O(1) = (1 - o(1)) log₂ n`.

The two together give the limit. Note the shape: the corollary is `o(1)`-asymptotic, but neither
input is — the asymptotics are entirely in the final squeeze, which is why this is publishable
as one bounded task on top of #56.
-/

open Finset

namespace PMC

section ListChromaticAsymptotic

/-- The list chromatic number of `K_{n,n}`: the least number of colours per list that always
suffices.

Defined as an `sInf` so that it is total with no side condition; the set is nonempty for every
`n` by Theorem 1.4.2 (`PMC.completeBipartiteChoosable_of_lt_two_pow` at any `k` with
`n < 2^{k-1}`), which is what keeps the value meaningful rather than the `sInf`-of-empty
default. -/
noncomputable def listChromaticBipartite (n : ℕ) : ℕ :=
  sInf {k | CompleteBipartiteChoosable n k}

/-- **Corollary 1.4.4.** `ch(K_{n,n}) / log₂ n → 1`. -/
theorem tendsto_listChromaticBipartite_div_logb :
    Filter.Tendsto (fun n => (listChromaticBipartite n : ℝ) / Real.logb 2 n)
      Filter.atTop (nhds 1) := by
  sorry

end ListChromaticAsymptotic

end PMC
