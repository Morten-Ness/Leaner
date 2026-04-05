import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R]

theorem iterate_derivative_natCast_mul {n k : ℕ} {f : R[X]} :
    Polynomial.derivative^[k] ((n : R[X]) * f) = n * Polynomial.derivative^[k] f := by
  induction k generalizing f <;> simp [*]

