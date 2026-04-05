import Mathlib

variable {A B : CommRingCat.{u}} (M : ModuleCat.{v} B) (f : A ⟶ B)

variable (D : M.Derivation f)

theorem d_mul (b b' : B) : D.d (b * b') = b • D.d b' + b' • D.d b := by simp [ModuleCat.Derivation.d]

