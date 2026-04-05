import Mathlib

variable {α n m : Type*}

variable [Mul α] [AddCommMonoid α]

variable (A : Matrix m n α)

theorem transpose_hasOrthogonalCols_iff_hasOrthogonalRows [Fintype n] :
    Aᵀ.HasOrthogonalCols ↔ A.HasOrthogonalRows := Iff.rfl

