import Mathlib

open scoped Nat

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R]

theorem derivative_C_mul_X (a : R) : Polynomial.derivative (Polynomial.C a * Polynomial.X) = Polynomial.C a := by
  simp [C_mul_X_eq_monomial, mul_one]

