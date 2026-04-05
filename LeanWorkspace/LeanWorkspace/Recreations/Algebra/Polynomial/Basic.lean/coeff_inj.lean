import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem coeff_inj : p.coeff = q.coeff ↔ p = q := Polynomial.coeff_injective.eq_iff

