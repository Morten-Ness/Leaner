import Mathlib

variable {ι : Sort*} {M : Type*} [MulOneClass M]

theorem op_top : (⊤ : Submonoid M).op = ⊤ := rfl

