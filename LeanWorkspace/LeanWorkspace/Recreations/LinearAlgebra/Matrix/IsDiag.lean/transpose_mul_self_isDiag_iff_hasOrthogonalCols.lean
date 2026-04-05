import Mathlib

variable {α β R n m : Type*}

theorem transpose_mul_self_isDiag_iff_hasOrthogonalCols [Fintype m] [Mul α] [AddCommMonoid α]
    {A : Matrix m n α} : (Aᵀ * A).IsDiag ↔ A.HasOrthogonalCols := Iff.rfl

