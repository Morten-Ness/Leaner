import Mathlib

variable {G : Type*} {P : Type*} [AddGroup G] [AddTorsor G P]

theorem pointReflection_vsub_right (x y : P) : Equiv.pointReflection x y -ᵥ y = 2 • (x -ᵥ y) := by
  rw [Equiv.pointReflection_apply, vadd_vsub_assoc, two_nsmul]
