import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p : R[X]}

variable {p q : R[X]} {ι : Type*}

theorem natDegree_C_mul_X_pow_le (a : R) (n : ℕ) : Polynomial.natDegree (Polynomial.C a * Polynomial.X ^ n) ≤ n := Polynomial.natDegree_le_iff_degree_le.2 <| Polynomial.degree_C_mul_X_pow_le _ _

