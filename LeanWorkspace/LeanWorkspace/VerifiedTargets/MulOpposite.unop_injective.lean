import Mathlib

variable {ι : Sort*} {M : Type*} [Mul M]

theorem unop_injective : (@Subsemigroup.unop M _).Injective := Subsemigroup.opEquiv.symm.injective

