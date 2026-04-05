import Mathlib

theorem comp_one {M₀ N₀ G₀ : Type*} [MulZeroOneClass M₀] [Nontrivial M₀] [NoZeroDivisors M₀]
    [MulZeroOneClass N₀] [MulZeroOneClass G₀] [DecidablePred fun x : M₀ ↦ x = 0]
    (f : N₀ →*₀ G₀) :
    f.comp (1 : M₀ →*₀ N₀) = (1 : M₀ →*₀ G₀) := ext <| MonoidWithZeroHom.apply_one_apply_eq _

