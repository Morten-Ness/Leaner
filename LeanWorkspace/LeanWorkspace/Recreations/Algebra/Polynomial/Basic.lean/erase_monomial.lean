import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem erase_monomial {n : ℕ} {a : R} : erase n (Polynomial.monomial n a) = 0 := Polynomial.toFinsupp_injective <| by simp

