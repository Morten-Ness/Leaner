import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R]

theorem iterate_derivative_zero {k : ℕ} : Polynomial.derivative^[k] (0 : R[X]) = 0 := iterate_map_zero Polynomial.derivative k

