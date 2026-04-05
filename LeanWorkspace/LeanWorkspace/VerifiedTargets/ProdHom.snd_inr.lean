import Mathlib

variable (G₀ H₀ : Type*) [GroupWithZero G₀] [GroupWithZero H₀]

theorem snd_inr [DecidablePred fun x : H₀ ↦ x = 0] (x : H₀) :
    MonoidWithZeroHom.snd _ _ (MonoidWithZeroHom.inr G₀ _ x) = x := by
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  simp [WithZero.withZeroUnitsEquiv, MonoidWithZeroHom.snd, MonoidWithZeroHom.inr]

