import Mathlib

variable (G₀ H₀ : Type*) [GroupWithZero G₀] [GroupWithZero H₀]

theorem fst_inl [DecidablePred fun x : G₀ ↦ x = 0] (x : G₀) :
    MonoidWithZeroHom.fst _ H₀ (MonoidWithZeroHom.inl _ _ x) = x := by
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  simp [WithZero.withZeroUnitsEquiv, MonoidWithZeroHom.fst, MonoidWithZeroHom.inl]

