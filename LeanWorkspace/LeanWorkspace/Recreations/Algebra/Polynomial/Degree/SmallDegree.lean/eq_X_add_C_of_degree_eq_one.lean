import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem eq_X_add_C_of_degree_eq_one (h : degree p = 1) :
    p = Polynomial.C p.leadingCoeff * Polynomial.X + Polynomial.C (p.coeff 0) := (Polynomial.eq_X_add_C_of_degree_le_one h.le).trans
    (by rw [← Nat.cast_one] at h; rw [leadingCoeff, natDegree_eq_of_degree_eq_some h])

