import Mathlib

variable {M₀ N₀ : Type*}

theorem inr_mono [GroupWithZero M₀] [Preorder M₀] [LinearOrderedCommGroupWithZero N₀]
    [DecidablePred fun x : N₀ ↦ x = 0] : Monotone (inr M₀ N₀) := by
  refine (WithZero.map'_mono MonoidHom.inr_mono).comp ?_
  intro x y
  obtain rfl | ⟨x, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  obtain rfl | ⟨y, rfl⟩ := GroupWithZero.eq_zero_or_unit y <;>
  · simp [WithZero.withZeroUnitsEquiv]

