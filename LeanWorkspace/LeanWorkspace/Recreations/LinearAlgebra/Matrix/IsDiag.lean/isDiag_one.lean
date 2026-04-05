import Mathlib

variable {α β R n m : Type*}

theorem isDiag_one [DecidableEq n] [Zero α] [One α] : (1 : Matrix n n α).IsDiag := fun _ _ =>
  one_apply_ne

