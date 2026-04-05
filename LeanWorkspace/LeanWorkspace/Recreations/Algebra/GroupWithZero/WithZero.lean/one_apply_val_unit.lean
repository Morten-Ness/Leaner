import Mathlib

theorem one_apply_val_unit {M₀ N₀ : Type*} [MonoidWithZero M₀] [MulZeroOneClass N₀]
    [DecidablePred fun x : M₀ ↦ x = 0] [Nontrivial M₀] [NoZeroDivisors M₀] (x : M₀ˣ) :
    (1 : M₀ →*₀ N₀) x = (1 : N₀) := one_apply_of_ne_zero x.ne_zero

