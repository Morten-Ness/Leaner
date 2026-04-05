import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Ring R]

theorem derivative_neg (f : R[X]) : Polynomial.derivative (-f) = -Polynomial.derivative f := map_neg Polynomial.derivative f

