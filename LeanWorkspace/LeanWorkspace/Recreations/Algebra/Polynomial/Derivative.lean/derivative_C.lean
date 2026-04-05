import Mathlib

open scoped Nat

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R]

theorem derivative_C {a : R} : Polynomial.derivative (Polynomial.C a) = 0 := by simp [Polynomial.derivative_apply]

