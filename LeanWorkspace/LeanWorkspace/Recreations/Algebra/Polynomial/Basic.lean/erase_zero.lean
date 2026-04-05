import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem erase_zero (n : ℕ) : (0 : R[X]).erase n = 0 := Polynomial.toFinsupp_injective <| by simp

