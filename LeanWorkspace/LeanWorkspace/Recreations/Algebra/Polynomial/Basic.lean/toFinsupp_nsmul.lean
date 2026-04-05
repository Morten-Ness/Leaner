import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem toFinsupp_nsmul (a : ℕ) (b : R[X]) : (a • b).toFinsupp = a • b.toFinsupp := rfl

