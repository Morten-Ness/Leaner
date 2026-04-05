import Mathlib

open scoped Nat

variable {R S : Type*}

variable [Semiring R] [Semiring S]

theorem sumIDeriv_map (p : R[X]) (f : R →+* S) :
    Polynomial.sumIDeriv (p.map f) = (Polynomial.sumIDeriv p).map f := by
  let n := max (p.map f).natDegree p.natDegree
  rw [Polynomial.sumIDeriv_apply_of_le (le_max_left _ _ : _ ≤ n)]
  rw [Polynomial.sumIDeriv_apply_of_le (le_max_right _ _ : _ ≤ n)]
  simp_rw [Polynomial.map_sum, iterate_derivative_map p f]

