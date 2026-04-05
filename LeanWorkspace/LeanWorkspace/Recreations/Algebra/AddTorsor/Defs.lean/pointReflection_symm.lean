import Mathlib

variable {G : Type*} {P : Type*} [AddGroup G] [AddTorsor G P]

theorem pointReflection_symm (x : P) : (Equiv.pointReflection x).symm = Equiv.pointReflection x := ext <| by simp [Equiv.pointReflection]

