import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R]

theorem derivative_zero : Polynomial.derivative (0 : R[X]) = 0 := Polynomial.derivative.map_zero

