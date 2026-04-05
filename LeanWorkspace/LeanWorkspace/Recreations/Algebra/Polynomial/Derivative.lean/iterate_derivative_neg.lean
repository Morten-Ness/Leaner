import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Ring R]

theorem iterate_derivative_neg {f : R[X]} {k : ℕ} : Polynomial.derivative^[k] (-f) = -Polynomial.derivative^[k] f := iterate_map_neg Polynomial.derivative k f

