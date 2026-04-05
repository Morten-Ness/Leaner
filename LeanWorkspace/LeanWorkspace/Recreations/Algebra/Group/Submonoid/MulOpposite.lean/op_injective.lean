import Mathlib

variable {ι : Sort*} {M : Type*} [MulOneClass M]

theorem op_injective : (@Submonoid.op M _).Injective := Submonoid.opEquiv.injective

