import Mathlib

variable {F A B C D : Type*}

variable [Mul A] [Mul B] [Mul C] [Mul D]

variable [Star A] [Star B] [Star C] [Star D]

theorem toMulEquiv_symm (f : A ≃⋆* B) : f.symm.toMulEquiv = f.toMulEquiv.symm := rfl

