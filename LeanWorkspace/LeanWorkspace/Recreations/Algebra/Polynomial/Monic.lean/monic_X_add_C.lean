import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Semiring R] {p q r : R[X]}

theorem monic_X_add_C (x : R) : Polynomial.Monic (Polynomial.X + Polynomial.C x) := pow_one (Polynomial.X : R[X]) ▸ Polynomial.monic_X_pow_add_C x one_ne_zero

