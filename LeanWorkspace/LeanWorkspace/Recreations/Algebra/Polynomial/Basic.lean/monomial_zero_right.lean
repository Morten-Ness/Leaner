import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem monomial_zero_right (n : ℕ) : Polynomial.monomial n (0 : R) = 0 := (Polynomial.monomial n).map_zero

-- This is not a `simp` lemma as `monomial_zero_left` is more general.

