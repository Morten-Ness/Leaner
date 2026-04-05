import Mathlib

variable (G₀ H₀ : Type*) [GroupWithZero G₀] [GroupWithZero H₀]

theorem inr_apply_unit [DecidablePred fun x : H₀ ↦ x = 0] (x : H₀ˣ) :
    MonoidWithZeroHom.inr G₀ H₀ x = (((1 : G₀ˣ), x) : WithZero (G₀ˣ × H₀ˣ)) := by
  simp [MonoidWithZeroHom.inr]

