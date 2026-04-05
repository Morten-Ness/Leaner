import Mathlib

variable (G₀ H₀ : Type*) [GroupWithZero G₀] [GroupWithZero H₀]

variable [DecidablePred fun x : G₀ ↦ x = 0] [DecidablePred fun x : H₀ ↦ x = 0]

theorem commute_inl_inr (m : G₀) (n : H₀) : Commute (MonoidWithZeroHom.inl G₀ H₀ m) (MonoidWithZeroHom.inr G₀ H₀ n) := by
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit m <;>
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit n <;>
  simp [MonoidWithZeroHom.inl, MonoidWithZeroHom.inr, WithZero.withZeroUnitsEquiv, commute_iff_eq, ← WithZero.coe_mul]

