import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem ext {p q : R[X]} : (∀ n, Polynomial.coeff p n = Polynomial.coeff q n) → p = q := Polynomial.ext_iff.2

