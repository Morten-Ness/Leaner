import Mathlib

variable {R : Type*} [Semiring R] (r : R) (f : R[X])

theorem degree_taylor (p : R[X]) (r : R) : degree (Polynomial.taylor r p) = degree p := by
  by_cases hp : p = 0
  · rw [hp, map_zero]
  · rw [degree_eq_natDegree hp, degree_eq_iff_natDegree_eq ((Polynomial.taylor_eq_zero r p).not.2 hp),
      Polynomial.natDegree_taylor]

