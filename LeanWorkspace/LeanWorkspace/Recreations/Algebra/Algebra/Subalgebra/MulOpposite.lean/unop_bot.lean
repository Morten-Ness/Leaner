import Mathlib

variable {ι : Sort*} {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem unop_bot : (⊥ : Subalgebra R Aᵐᵒᵖ).unop = ⊥ := Subalgebra.opEquiv.symm.map_bot

