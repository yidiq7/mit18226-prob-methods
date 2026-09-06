import ProbMethods.Basic

/-!
# Gate self-test

A throwaway declaration used once, by the orchestrator, to drive `verify-comparator`
through its full kernel-level path on a PR that has a real task target. Deleted
immediately afterwards; it is not part of the formalization.
-/

namespace PMC

/-- Gate self-test. Not mathematics. -/
theorem gate_self_test (n : ℕ) : n + 0 = n := by
  sorry

end PMC
