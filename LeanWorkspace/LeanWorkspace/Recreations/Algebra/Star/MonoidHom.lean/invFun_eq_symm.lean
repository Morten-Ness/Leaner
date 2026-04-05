import Mathlib

variable {F A B C D : Type*}

variable [Mul A] [Mul B] [Mul C] [Mul D]

variable [Star A] [Star B] [Star C] [Star D]

theorem invFun_eq_symm {e : A ≃⋆* B} : EquivLike.inv e = e.symm := rfl

