import Mathlib

variable {α β n R : Type*}

theorem conjTranspose_circulant [Star α] [SubtractionMonoid n] (v : n → α) :
    (Matrix.circulant v)ᴴ = Matrix.circulant (star fun i => v (-i)) := by ext; simp

