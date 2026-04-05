import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem C_inj : Polynomial.C a = Polynomial.C b ↔ a = b := Polynomial.C_injective.eq_iff

