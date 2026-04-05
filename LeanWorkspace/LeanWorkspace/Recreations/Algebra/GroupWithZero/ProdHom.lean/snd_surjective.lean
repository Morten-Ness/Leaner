import Mathlib

variable (G₀ H₀ : Type*) [GroupWithZero G₀] [GroupWithZero H₀]

theorem snd_surjective : Function.Surjective (MonoidWithZeroHom.snd G₀ H₀) := by
  classical
  exact Function.HasRightInverse.surjective ⟨MonoidWithZeroHom.inr .., fun _ ↦ by simp⟩

