FAIL
import Mathlib

variable {G : Type*} {P : Type*} [AddGroup G] [AddTorsor G P]

theorem pointReflection_involutive (x : P) : Function.Involutive (Equiv.pointReflection x : P → P) := by
  intro y
  dsimp [Equiv.pointReflection]
  rw [vsub_vadd, vsub_vadd]
  abel
