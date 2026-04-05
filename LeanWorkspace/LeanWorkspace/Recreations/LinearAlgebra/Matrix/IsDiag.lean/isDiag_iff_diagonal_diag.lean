import Mathlib

variable {α β R n m : Type*}

theorem isDiag_iff_diagonal_diag [Zero α] [DecidableEq n] (A : Matrix n n α) :
    A.IsDiag ↔ diagonal (diag A) = A := ⟨Matrix.IsDiag.diagonal_diag, fun hd => hd ▸ Matrix.isDiag_diagonal (diag A)⟩

