import Mathlib

variable {ι : Sort*} {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem op_bot : (⊥ : Subalgebra R A).op = ⊥ := Subalgebra.opEquiv.map_bot

