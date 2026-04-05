import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem degree_monomial_le (n : ℕ) (a : R) : Polynomial.degree (monomial n a) ≤ n := letI := Classical.decEq R
  if h : a = 0 then by rw [h, (monomial n).map_zero, Polynomial.degree_zero]; exact bot_le
  else le_of_eq (Polynomial.degree_monomial n h)

