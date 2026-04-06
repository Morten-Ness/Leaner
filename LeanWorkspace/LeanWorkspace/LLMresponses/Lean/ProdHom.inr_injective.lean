FAIL
import Mathlib

variable (G₀ H₀ : Type*) [GroupWithZero G₀] [GroupWithZero H₀]

theorem inr_injective [DecidablePred fun x : H₀ ↦ x = 0] :
    Function.Injective (MonoidWithZeroHom.inr G₀ H₀) := by
  intro x y h
  change Prod.snd ((MonoidWithZeroHom.inr G₀ H₀) x) = Prod.snd ((MonoidWithZeroHom.inr G₀ H₀) y) at h
  simpa [MonoidWithZeroHom.inr] using h
