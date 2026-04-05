import Mathlib

open scoped Polynomial

variable (p q : ℤ[X])

theorem leadingCoeff_isUnit (hp : p.IsUnitTrinomial) : IsUnit p.leadingCoeff := Polynomial.IsUnitTrinomial.coeff_isUnit hp (natDegree_mem_support_of_nonzero Polynomial.IsUnitTrinomial.ne_zero hp)

