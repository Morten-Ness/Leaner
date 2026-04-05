import Mathlib

variable {M₀ N₀ : Type*}

theorem inl_mono [LinearOrderedCommGroupWithZero M₀] [GroupWithZero N₀] [Preorder N₀]
    [DecidablePred fun x : M₀ ↦ x = 0] : Monotone (inl M₀ N₀) := by
  refine (WithZero.map'_mono MonoidHom.inl_mono).comp ?_
  intro x y
  obtain rfl | ⟨x, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  obtain rfl | ⟨y, rfl⟩ := GroupWithZero.eq_zero_or_unit y <;>
  · simp [WithZero.withZeroUnitsEquiv]

