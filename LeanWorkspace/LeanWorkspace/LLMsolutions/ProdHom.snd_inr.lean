import Mathlib

variable (G₀ H₀ : Type*) [GroupWithZero G₀] [GroupWithZero H₀]

theorem snd_inr [DecidablePred fun x : H₀ ↦ x = 0] (x : H₀) :
    MonoidWithZeroHom.snd _ _ (MonoidWithZeroHom.inr G₀ _ x) = x := by
  by_cases hx : x = 0
  · simp [MonoidWithZeroHom.inr, MonoidWithZeroHom.snd, hx]
  · simp [MonoidWithZeroHom.inr, MonoidWithZeroHom.snd, hx]
