import Mathlib

variable {α β n R : Type*}

theorem circulant_neg [Neg α] [Sub n] (v : n → α) : Matrix.circulant (-v) = -Matrix.circulant v := ext fun _ _ => rfl

