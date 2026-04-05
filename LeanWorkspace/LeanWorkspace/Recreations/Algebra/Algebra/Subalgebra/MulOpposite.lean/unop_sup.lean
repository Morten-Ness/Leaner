import Mathlib

variable {ι : Sort*} {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem unop_sup (S₁ S₂ : Subalgebra R Aᵐᵒᵖ) : (S₁ ⊔ S₂).unop = S₁.unop ⊔ S₂.unop := Subalgebra.opEquiv.symm.map_sup _ _

