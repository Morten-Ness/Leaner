import Mathlib

variable {G : Type*} {P : Type*} [AddGroup G] [AddTorsor G P]

theorem pointReflection_vsub_left (x y : P) : Equiv.pointReflection x y -ᵥ x = x -ᵥ y := vadd_vsub ..

