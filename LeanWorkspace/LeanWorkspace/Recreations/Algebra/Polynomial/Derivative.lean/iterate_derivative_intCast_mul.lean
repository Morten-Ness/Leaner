import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Ring R]

theorem iterate_derivative_intCast_mul {n : ℤ} {k : ℕ} {f : R[X]} :
    Polynomial.derivative^[k] ((n : R[X]) * f) = n * Polynomial.derivative^[k] f := by
  induction k generalizing f <;> simp [*]

