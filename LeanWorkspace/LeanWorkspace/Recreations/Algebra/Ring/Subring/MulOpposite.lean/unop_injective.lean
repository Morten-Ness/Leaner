import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocRing R]

theorem unop_injective : (@Subring.unop R _).Injective := Subring.opEquiv.symm.injective

