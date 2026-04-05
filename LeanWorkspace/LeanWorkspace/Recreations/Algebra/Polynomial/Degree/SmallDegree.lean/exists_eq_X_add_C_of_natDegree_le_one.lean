import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem exists_eq_X_add_C_of_natDegree_le_one (h : natDegree p ≤ 1) : ∃ a b, p = Polynomial.C a * Polynomial.X + Polynomial.C b := ⟨p.coeff 1, p.coeff 0, Polynomial.eq_X_add_C_of_natDegree_le_one h⟩

