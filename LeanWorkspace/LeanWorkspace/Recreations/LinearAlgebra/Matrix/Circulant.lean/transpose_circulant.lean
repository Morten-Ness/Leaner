import Mathlib

variable {α β n R : Type*}

theorem transpose_circulant [SubtractionMonoid n] (v : n → α) :
    (Matrix.circulant v)ᵀ = Matrix.circulant fun i => v (-i) := by ext; simp

