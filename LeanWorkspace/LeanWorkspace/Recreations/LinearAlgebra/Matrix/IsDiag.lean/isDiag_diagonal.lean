import Mathlib

variable {α β R n m : Type*}

theorem isDiag_diagonal [Zero α] [DecidableEq n] (d : n → α) : (diagonal d).IsDiag := fun _ _ =>
  Matrix.diagonal_apply_ne _

