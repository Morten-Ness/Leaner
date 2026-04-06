FAIL
import Mathlib

variable (G₀ H₀ : Type*) [GroupWithZero G₀] [GroupWithZero H₀]

theorem snd_comp_inr [DecidablePred fun x : H₀ ↦ x = 0] :
    (MonoidWithZeroHom.snd ..).comp (MonoidWithZeroHom.inr G₀ H₀) = .id _ := by
  ext x
  simp [MonoidWithZeroHom.inr, MonoidWithZeroHom.snd]
