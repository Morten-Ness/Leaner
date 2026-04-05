import Mathlib

variable {F α β γ δ M₀ : Type*} [MulZeroOneClass α] [MulZeroOneClass β] [MulZeroOneClass γ]
  [MulZeroOneClass δ]

variable [FunLike F α β]

theorem one_apply_of_ne_zero {M₀ N₀ : Type*} [MulZeroOneClass M₀] [MulZeroOneClass N₀]
    [DecidablePred fun x : M₀ ↦ x = 0] [Nontrivial M₀] [NoZeroDivisors M₀] {x : M₀} (hx : x ≠ 0) :
    (1 : M₀ →*₀ N₀) x = 1 := if_neg hx

