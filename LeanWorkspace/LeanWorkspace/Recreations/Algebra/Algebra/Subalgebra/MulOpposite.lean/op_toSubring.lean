import Mathlib

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

theorem op_toSubring (S : Subalgebra R A) : S.op.toSubring = S.toSubring.op := rfl

