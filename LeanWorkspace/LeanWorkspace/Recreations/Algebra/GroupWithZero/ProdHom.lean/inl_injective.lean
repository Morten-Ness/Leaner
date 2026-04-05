import Mathlib

variable (G₀ H₀ : Type*) [GroupWithZero G₀] [GroupWithZero H₀]

theorem inl_injective [DecidablePred fun x : G₀ ↦ x = 0] :
    Function.Injective (MonoidWithZeroHom.inl G₀ H₀) := Function.HasLeftInverse.injective ⟨MonoidWithZeroHom.fst .., fun _ ↦ by simp⟩

