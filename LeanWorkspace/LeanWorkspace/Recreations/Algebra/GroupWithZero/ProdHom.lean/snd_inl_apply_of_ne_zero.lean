import Mathlib

variable (G₀ H₀ : Type*) [GroupWithZero G₀] [GroupWithZero H₀]

theorem snd_inl_apply_of_ne_zero [DecidablePred fun x : G₀ ↦ x = 0] {x : G₀} (hx : x ≠ 0) :
    MonoidWithZeroHom.snd _ _ (MonoidWithZeroHom.inl _ H₀ x) = 1 := by
  rw [← MonoidWithZeroHom.comp_apply, MonoidWithZeroHom.snd_comp_inl, one_apply_of_ne_zero hx]

