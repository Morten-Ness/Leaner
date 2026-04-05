import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Semiring R] {p q r : R[X]}

theorem monic_zero_iff_subsingleton : Polynomial.Monic (0 : R[X]) ↔ Subsingleton R := subsingleton_iff_zero_eq_one

