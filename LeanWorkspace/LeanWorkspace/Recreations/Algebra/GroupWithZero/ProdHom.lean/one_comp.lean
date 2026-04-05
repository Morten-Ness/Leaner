import Mathlib

theorem one_comp {M₀ N₀ G₀ : Type*}
    [GroupWithZero M₀]
    [MulZeroOneClass N₀] [Nontrivial N₀] [NoZeroDivisors N₀]
    [MulZeroOneClass G₀]
    [DecidablePred fun x : M₀ ↦ x = 0] [DecidablePred fun x : N₀ ↦ x = 0]
    (f : M₀ →*₀ N₀) :
    (1 : N₀ →*₀ G₀).comp f = (1 : M₀ →*₀ G₀) := ext <| MonoidWithZeroHom.one_apply_apply_eq _

