import Mathlib

variable {F α β γ δ M₀ : Type*} [MulZeroOneClass α] [MulZeroOneClass β] [MulZeroOneClass γ]
  [MulZeroOneClass δ]

variable [FunLike F α β]

theorem copy_eq (f : α →*₀ β) (f' : α → β) (h) : f.copy f' h = f := DFunLike.ext' h

protected lemma map_one (f : α →*₀ β) : f 1 = 1 := f.map_one'

protected lemma map_zero (f : α →*₀ β) : f 0 = 0 := f.map_zero'

protected lemma map_mul (f : α →*₀ β) (a b : α) : f (a * b) = f a * f b := f.map_mul' a b

