import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem leadingCoeff_add_of_degree_lt (h : degree p < degree q) :
    leadingCoeff (p + q) = leadingCoeff q := by
  have : coeff p (natDegree q) = 0 := Polynomial.coeff_natDegree_eq_zero_of_degree_lt h
  simp only [leadingCoeff, natDegree_eq_of_degree_eq (Polynomial.degree_add_eq_right_of_degree_lt h), this,
    coeff_add, zero_add]

