import Mathlib

variable {R : Type*} [Semiring R] (p q : R[X])

theorem mirror_natDegree : p.mirror.natDegree = p.natDegree := by
  by_cases hp : p = 0
  · rw [hp, Polynomial.mirror_zero]
  nontriviality R
  rw [Polynomial.mirror, natDegree_mul', reverse_natDegree, natDegree_X_pow,
    tsub_add_cancel_of_le p.natTrailingDegree_le_natDegree]
  rwa [leadingCoeff_X_pow, mul_one, reverse_leadingCoeff, Ne, trailingCoeff_eq_zero]

