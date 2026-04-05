import Mathlib

variable {G : Type*} {P : Type*} [AddGroup G] [AddTorsor G P]

theorem pointReflection_involutive (x : P) : Function.Involutive (Equiv.pointReflection x : P → P) := fun y =>
  (Equiv.apply_eq_iff_eq_symm_apply _).2 <| by rw [Equiv.pointReflection_symm]

