import Mathlib

variable {α n m : Type*}

variable [Mul α] [AddCommMonoid α]

variable (A : Matrix m n α)

theorem HasOrthogonalRows.transpose_hasOrthogonalCols [Fintype n] (h : A.HasOrthogonalRows) :
    Aᵀ.HasOrthogonalCols := h

