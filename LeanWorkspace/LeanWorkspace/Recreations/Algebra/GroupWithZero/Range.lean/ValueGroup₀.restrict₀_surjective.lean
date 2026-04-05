import Mathlib

variable [GroupWithZero A] [GroupWithZero B] [MonoidWithZeroHomClass F A B] {f}

theorem ValueGroup₀.restrict₀_surjective : Function.Surjective (MonoidWithZeroHom.ValueGroup₀.restrict₀ f) := fun _ ↦ mem_range.mp (by simp [ValueGroup₀.restrict₀_range_eq_top])

