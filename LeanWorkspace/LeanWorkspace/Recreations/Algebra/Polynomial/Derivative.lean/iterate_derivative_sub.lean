import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Ring R]

theorem iterate_derivative_sub {k : ℕ} {f g : R[X]} :
    Polynomial.derivative^[k] (f - g) = Polynomial.derivative^[k] f - Polynomial.derivative^[k] g := iterate_map_sub Polynomial.derivative k f g

