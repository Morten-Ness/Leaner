import Mathlib

variable {α β n R : Type*}

theorem circulant_sub [Sub α] [Sub n] (v w : n → α) :
    Matrix.circulant (v - w) = Matrix.circulant v - Matrix.circulant w := ext fun _ _ => rfl

