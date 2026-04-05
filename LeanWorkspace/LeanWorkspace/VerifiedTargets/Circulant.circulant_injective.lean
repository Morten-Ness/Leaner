import Mathlib

variable {α β n R : Type*}

theorem circulant_injective [SubtractionMonoid n] :
    Function.Injective (Matrix.circulant : (n → α) → Matrix n n α) := by
  intro v w h
  ext k
  rw [← Matrix.circulant_col_zero_eq v, ← Matrix.circulant_col_zero_eq w, h]

