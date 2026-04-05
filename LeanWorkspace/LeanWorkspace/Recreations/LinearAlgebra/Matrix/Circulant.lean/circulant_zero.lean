import Mathlib

variable {α β n R : Type*}

theorem circulant_zero (α n) [Zero α] [Sub n] : Matrix.circulant 0 = (0 : Matrix n n α) := ext fun _ _ => rfl

