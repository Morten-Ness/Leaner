import Mathlib

variable {α β n R : Type*}

theorem map_circulant [Sub n] (v : n → α) (f : α → β) :
    (Matrix.circulant v).map f = Matrix.circulant fun i => f (v i) := ext fun _ _ => rfl

