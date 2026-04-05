import Mathlib

variable {α β n R : Type*}

theorem circulant_apply [Sub n] (v : n → α) (i j) : Matrix.circulant v i j = v (i - j) := rfl

