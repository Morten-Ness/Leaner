import Mathlib

open scoped Nat

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R]

theorem derivative_monomial_succ (a : R) (n : ℕ) :
    Polynomial.derivative (monomial (n + 1) a) = monomial n (a * (n + 1)) := by
  rw [Polynomial.derivative_monomial, add_tsub_cancel_right, Nat.cast_add, Nat.cast_one]

