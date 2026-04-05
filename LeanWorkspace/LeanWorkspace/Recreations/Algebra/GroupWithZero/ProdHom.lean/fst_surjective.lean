import Mathlib

variable (G₀ H₀ : Type*) [GroupWithZero G₀] [GroupWithZero H₀]

theorem fst_surjective : Function.Surjective (MonoidWithZeroHom.fst G₀ H₀) := by
  classical
  exact Function.HasRightInverse.surjective ⟨MonoidWithZeroHom.inl .., fun _ ↦ by simp⟩

