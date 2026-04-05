import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Ring R]

theorem ofFinsupp_zsmul (a : ℤ) (b) :
    (⟨a • b⟩ : R[X]) = (a • ⟨b⟩ : R[X]) := rfl

