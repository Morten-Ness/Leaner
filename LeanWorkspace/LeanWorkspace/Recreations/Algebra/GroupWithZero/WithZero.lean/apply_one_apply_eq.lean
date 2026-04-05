import Mathlib

theorem apply_one_apply_eq {M₀ N₀ G₀ : Type*} [MulZeroOneClass M₀] [Nontrivial M₀] [NoZeroDivisors M₀]
    [MulZeroOneClass N₀] [MulZeroOneClass G₀] [DecidablePred fun x : M₀ ↦ x = 0]
    (f : N₀ →*₀ G₀) (x : M₀) :
    f ((1 : M₀ →*₀ N₀) x) = (1 : M₀ →*₀ G₀) x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [one_apply_of_ne_zero hx, one_apply_of_ne_zero hx, map_one]

