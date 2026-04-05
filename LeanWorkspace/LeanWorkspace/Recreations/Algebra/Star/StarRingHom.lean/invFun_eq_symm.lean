import Mathlib

variable {A B C : Type*} [Add A] [Add B] [Mul A] [Mul B] [Star A] [Star B] [Add C] [Mul C] [Star C]

theorem invFun_eq_symm {e : A ≃⋆+* B} : EquivLike.inv e = e.symm := rfl

