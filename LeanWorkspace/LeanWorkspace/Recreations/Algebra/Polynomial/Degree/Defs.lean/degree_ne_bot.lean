import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem degree_ne_bot : Polynomial.degree p ≠ ⊥ ↔ p ≠ 0 := Polynomial.degree_eq_bot.not

