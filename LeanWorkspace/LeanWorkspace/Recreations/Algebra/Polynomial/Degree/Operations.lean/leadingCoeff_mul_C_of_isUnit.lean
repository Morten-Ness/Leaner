import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem leadingCoeff_mul_C_of_isUnit (ha : IsUnit a) (p : R[X]) :
    (p * Polynomial.C a).leadingCoeff = p.leadingCoeff * a := by
  rwa [leadingCoeff, coeff_mul_C, Polynomial.natDegree_mul_C_of_isUnit, leadingCoeff]

