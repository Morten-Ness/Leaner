import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Semiring R] {p q r : R[X]}

theorem not_monic_zero_iff : ¬Polynomial.Monic (0 : R[X]) ↔ (0 : R) ≠ 1 := (Polynomial.monic_zero_iff_subsingleton.trans subsingleton_iff_zero_eq_one.symm).not

