import Mathlib

variable {α β R n m : Type*}

theorem isDiag_zero [Zero α] : (0 : Matrix n n α).IsDiag := fun _ _ _ => rfl

