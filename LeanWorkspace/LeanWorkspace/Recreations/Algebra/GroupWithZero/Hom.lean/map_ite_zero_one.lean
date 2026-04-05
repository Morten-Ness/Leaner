import Mathlib

variable {F α β γ δ M₀ : Type*} [MulZeroOneClass α] [MulZeroOneClass β] [MulZeroOneClass γ]
  [MulZeroOneClass δ]

variable [FunLike F α β]

theorem map_ite_zero_one {F : Type*} [FunLike F α β] [MonoidWithZeroHomClass F α β] (f : F)
    (p : Prop) [Decidable p] :
    f (ite p 0 1) = ite p 0 1 := by
  split_ifs with h <;> simp

