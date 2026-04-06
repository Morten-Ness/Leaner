import Mathlib

variable {F α β γ δ M₀ : Type*} [MulZeroOneClass α] [MulZeroOneClass β] [MulZeroOneClass γ]
  [MulZeroOneClass δ]

variable [FunLike F α β]

theorem one_apply_eq_zero_iff {M₀ N₀ : Type*} [MulZeroOneClass M₀] [MulZeroOneClass N₀]
    [DecidablePred fun x : M₀ ↦ x = 0] [Nontrivial M₀] [NoZeroDivisors M₀] [Nontrivial N₀]
    {x : M₀} :
    (1 : M₀ →*₀ N₀) x = 0 ↔ x = 0 := by
  simp [OneHom.toFun_eq_coe, Pi.one_apply]
