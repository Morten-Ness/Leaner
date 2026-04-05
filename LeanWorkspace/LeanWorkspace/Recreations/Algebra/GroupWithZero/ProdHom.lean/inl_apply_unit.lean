import Mathlib

variable (G₀ H₀ : Type*) [GroupWithZero G₀] [GroupWithZero H₀]

theorem inl_apply_unit [DecidablePred fun x : G₀ ↦ x = 0] (x : G₀ˣ) :
    MonoidWithZeroHom.inl G₀ H₀ x = ((x, (1 : H₀ˣ)) : WithZero (G₀ˣ × H₀ˣ)) := by
  simp [MonoidWithZeroHom.inl]

