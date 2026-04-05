import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem monomial_eq_zero_iff (t : R) (n : ℕ) : Polynomial.monomial n t = 0 ↔ t = 0 := LinearMap.map_eq_zero_iff _ (Polynomial.monomial_injective n)

