import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem coeff_natCast_ite : (Nat.cast m : R[X]).coeff n = ite (n = 0) m 0 := by
  simp only [← Polynomial.C_eq_natCast, Polynomial.coeff_C, Nat.cast_ite, Nat.cast_zero]

