import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Ring R]

theorem toFinsupp_zsmul (a : ℤ) (b : R[X]) :
    (a • b).toFinsupp = a • b.toFinsupp := rfl

