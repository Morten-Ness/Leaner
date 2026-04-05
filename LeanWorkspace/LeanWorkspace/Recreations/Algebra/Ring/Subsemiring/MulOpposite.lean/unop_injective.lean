import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocSemiring R]

theorem unop_injective : (@Subsemiring.unop R _).Injective := Subsemiring.opEquiv.symm.injective

