import Mathlib

open scoped Polynomial

variable (p q : ℤ[X])

theorem trailingCoeff_isUnit (hp : p.IsUnitTrinomial) : IsUnit p.trailingCoeff := Polynomial.IsUnitTrinomial.coeff_isUnit hp (natTrailingDegree_mem_support_of_nonzero Polynomial.IsUnitTrinomial.ne_zero hp)

