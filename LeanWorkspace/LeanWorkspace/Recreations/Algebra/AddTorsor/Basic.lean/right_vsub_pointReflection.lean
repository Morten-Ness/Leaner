import Mathlib

open scoped Pointwise

variable (G : Type*) (P : Type*) [AddGroup G] [AddTorsor G P]

theorem right_vsub_pointReflection (x y : P) : y -ᵥ pointReflection x y = 2 • (y -ᵥ x) := neg_injective <| by simp [← neg_nsmul]

