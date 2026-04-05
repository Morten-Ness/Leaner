import Mathlib

variable (G₀ H₀ : Type*) [GroupWithZero G₀] [GroupWithZero H₀]

theorem snd_comp_inl [DecidablePred fun x : G₀ ↦ x = 0] :
    (MonoidWithZeroHom.snd ..).comp (MonoidWithZeroHom.inl G₀ H₀) = 1 := by
  ext x
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  simp_all [WithZero.withZeroUnitsEquiv, MonoidWithZeroHom.snd, MonoidWithZeroHom.inl]

