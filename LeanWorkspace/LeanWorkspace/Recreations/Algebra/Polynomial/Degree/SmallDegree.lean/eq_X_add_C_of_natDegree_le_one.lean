import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem eq_X_add_C_of_natDegree_le_one (h : natDegree p ≤ 1) :
    p = Polynomial.C (p.coeff 1) * Polynomial.X + Polynomial.C (p.coeff 0) := Polynomial.eq_X_add_C_of_degree_le_one <| degree_le_of_natDegree_le h

