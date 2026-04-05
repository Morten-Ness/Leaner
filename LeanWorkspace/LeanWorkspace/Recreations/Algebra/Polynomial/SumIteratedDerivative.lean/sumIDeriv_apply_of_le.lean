import Mathlib

open scoped Nat

variable {R S : Type*}

variable [Semiring R] [Semiring S]

theorem sumIDeriv_apply_of_le {p : R[X]} {n : ℕ} (hn : p.natDegree ≤ n) :
    Polynomial.sumIDeriv p = ∑ i ∈ range (n + 1), derivative^[i] p := by
  dsimp [Polynomial.sumIDeriv]
  exact Finsupp.sum_of_support_subset _ (by simp [hn]) _ (by simp)

