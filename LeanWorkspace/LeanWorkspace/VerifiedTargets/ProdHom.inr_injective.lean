import Mathlib

variable (G₀ H₀ : Type*) [GroupWithZero G₀] [GroupWithZero H₀]

theorem inr_injective [DecidablePred fun x : H₀ ↦ x = 0] :
    Function.Injective (MonoidWithZeroHom.inr G₀ H₀) := Function.HasLeftInverse.injective ⟨MonoidWithZeroHom.snd .., fun _ ↦ by simp⟩

