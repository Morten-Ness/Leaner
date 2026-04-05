import Mathlib

variable {ι : Sort*} {M : Type*} [Mul M]

theorem op_injective : (@Subsemigroup.op M _).Injective := Subsemigroup.opEquiv.injective

