import Mathlib

variable {α β R n m : Type*}

theorem isDiag_transpose_iff [Zero α] {A : Matrix n n α} : Aᵀ.IsDiag ↔ A.IsDiag := ⟨Matrix.IsDiag.transpose, Matrix.IsDiag.transpose⟩

