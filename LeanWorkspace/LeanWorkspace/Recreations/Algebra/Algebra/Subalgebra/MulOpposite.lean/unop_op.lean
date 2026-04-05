import Mathlib

variable {ι : Sort*} {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem unop_op (S : Subalgebra R A) : S.op.unop = S := rfl

