import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem C_ofNat (n : ℕ) [n.AtLeastTwo] : Polynomial.C ofNat(n) = (ofNat(n) : R[X]) := rfl

