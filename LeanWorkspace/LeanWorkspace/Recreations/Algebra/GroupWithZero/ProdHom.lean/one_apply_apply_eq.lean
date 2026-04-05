import Mathlib

theorem one_apply_apply_eq {M₀ N₀ G₀ : Type*}
    [GroupWithZero M₀]
    [MulZeroOneClass N₀] [Nontrivial N₀] [NoZeroDivisors N₀]
    [MulZeroOneClass G₀]
    [DecidablePred fun x : M₀ ↦ x = 0] [DecidablePred fun x : N₀ ↦ x = 0]
    (f : M₀ →*₀ N₀) (x : M₀) :
    (1 : N₀ →*₀ G₀) (f x) = (1 : M₀ →*₀ G₀) x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [one_apply_of_ne_zero hx, one_apply_of_ne_zero]
    rwa [map_ne_zero f]

