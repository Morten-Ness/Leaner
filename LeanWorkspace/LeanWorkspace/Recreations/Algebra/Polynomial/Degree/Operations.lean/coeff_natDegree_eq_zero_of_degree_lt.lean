import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem coeff_natDegree_eq_zero_of_degree_lt (h : degree p < degree q) :
    coeff p (natDegree q) = 0 := Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le h Polynomial.degree_le_natDegree)

