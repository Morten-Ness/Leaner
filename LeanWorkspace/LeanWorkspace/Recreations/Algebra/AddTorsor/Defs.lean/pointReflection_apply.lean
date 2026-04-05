import Mathlib

variable {G : Type*} {P : Type*} [AddGroup G] [AddTorsor G P]

theorem pointReflection_apply (x y : P) : Equiv.pointReflection x y = (x -ᵥ y) +ᵥ x := rfl

