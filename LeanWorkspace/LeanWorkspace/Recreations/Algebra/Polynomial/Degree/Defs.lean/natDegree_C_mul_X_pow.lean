import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem natDegree_C_mul_X_pow (n : ℕ) (a : R) (ha : a ≠ 0) : Polynomial.natDegree (Polynomial.C a * Polynomial.X ^ n) = n := Polynomial.natDegree_eq_of_degree_eq_some (Polynomial.degree_C_mul_X_pow n ha)

