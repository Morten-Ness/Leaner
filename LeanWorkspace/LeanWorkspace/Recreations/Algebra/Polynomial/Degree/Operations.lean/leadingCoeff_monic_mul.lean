import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem leadingCoeff_monic_mul {p q : R[X]} (hp : Polynomial.Monic p) :
    leadingCoeff (p * q) = leadingCoeff q := by
  rcases eq_or_ne q 0 with (rfl | H)
  · simp
  · rw [Polynomial.leadingCoeff_mul', hp.leadingCoeff, one_mul]
    rwa [hp.leadingCoeff, one_mul, Ne, leadingCoeff_eq_zero]

