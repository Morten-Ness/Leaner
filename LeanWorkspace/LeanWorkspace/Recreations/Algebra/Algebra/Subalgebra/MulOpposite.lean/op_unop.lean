import Mathlib

variable {ι : Sort*} {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem op_unop (S : Subalgebra R Aᵐᵒᵖ) : S.unop.op = S := rfl

