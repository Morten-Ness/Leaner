import Mathlib

variable {ι : Sort*} {M : Type*} [Mul M]

theorem op_bot : (⊥ : Subsemigroup M).op = ⊥ := Subsemigroup.opEquiv.map_bot

