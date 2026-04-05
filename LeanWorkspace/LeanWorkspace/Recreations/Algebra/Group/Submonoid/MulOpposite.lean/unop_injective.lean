import Mathlib

variable {ι : Sort*} {M : Type*} [MulOneClass M]

theorem unop_injective : (@Submonoid.unop M _).Injective := Submonoid.opEquiv.symm.injective

