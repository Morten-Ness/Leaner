import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocSemiring R]

theorem op_injective : (@Subsemiring.op R _).Injective := Subsemiring.opEquiv.injective

