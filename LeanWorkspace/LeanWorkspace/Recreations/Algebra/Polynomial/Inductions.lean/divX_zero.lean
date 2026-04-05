import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem divX_zero : Polynomial.divX (0 : R[X]) = 0 := leadingCoeff_eq_zero.mp rfl

