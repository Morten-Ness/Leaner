import Mathlib

variable {ι : Sort*} {M : Type*} [MulOneClass M]

theorem op_bot : (⊥ : Submonoid M).op = ⊥ := Submonoid.opEquiv.map_bot

