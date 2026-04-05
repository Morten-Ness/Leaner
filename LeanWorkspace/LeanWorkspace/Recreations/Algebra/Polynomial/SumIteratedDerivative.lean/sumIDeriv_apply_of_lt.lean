import Mathlib

open scoped Nat

variable {R S : Type*}

variable [Semiring R] [Semiring S]

theorem sumIDeriv_apply_of_lt {p : R[X]} {n : ℕ} (hn : p.natDegree < n) :
    Polynomial.sumIDeriv p = ∑ i ∈ range n, derivative^[i] p := by
  dsimp [Polynomial.sumIDeriv]
  exact Finsupp.sum_of_support_subset _ (by simp [hn]) _ (by simp)

