import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Semiring R] [Nontrivial R] {p q : R[X]}

theorem not_monic_zero : ¬Polynomial.Monic (0 : R[X]) := Polynomial.not_monic_zero_iff.mp zero_ne_one

