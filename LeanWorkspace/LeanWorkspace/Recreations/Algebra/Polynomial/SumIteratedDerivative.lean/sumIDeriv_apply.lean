import Mathlib

open scoped Nat

variable {R S : Type*}

variable [Semiring R] [Semiring S]

theorem sumIDeriv_apply (p : R[X]) :
    Polynomial.sumIDeriv p = ∑ i ∈ range (p.natDegree + 1), derivative^[i] p := by
  dsimp [Polynomial.sumIDeriv]
  exact Finsupp.sum_of_support_subset _ (by simp) _ (by simp)

