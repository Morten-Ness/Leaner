FAIL
import Mathlib

variable (G₀ H₀ : Type*) [GroupWithZero G₀] [GroupWithZero H₀]

theorem snd_comp_inl [DecidablePred fun x : G₀ ↦ x = 0] :
    (MonoidWithZeroHom.snd ..).comp (MonoidWithZeroHom.inl G₀ H₀) = 1 := by
  ext x
  by_cases h : x = 0
  · simp [MonoidWithZeroHom.inl, MonoidWithZeroHom.snd, h]
  · simp [MonoidWithZeroHom.inl, MonoidWithZeroHom.snd, h]
