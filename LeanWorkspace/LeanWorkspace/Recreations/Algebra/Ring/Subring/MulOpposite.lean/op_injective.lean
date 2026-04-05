import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocRing R]

theorem op_injective : (@Subring.op R _).Injective := Subring.opEquiv.injective

