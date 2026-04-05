import Mathlib

variable {G : Type*} {P : Type*} [AddGroup G] [AddTorsor G P]

theorem pointReflection_self (x : P) : Equiv.pointReflection x x = x := vsub_vadd _ _

