import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R]

theorem derivative_add {f g : R[X]} : Polynomial.derivative (f + g) = Polynomial.derivative f + Polynomial.derivative g := Polynomial.derivative.map_add f g

