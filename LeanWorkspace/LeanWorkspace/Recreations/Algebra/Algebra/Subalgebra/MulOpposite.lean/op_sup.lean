import Mathlib

variable {ι : Sort*} {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem op_sup (S₁ S₂ : Subalgebra R A) : (S₁ ⊔ S₂).op = S₁.op ⊔ S₂.op := Subalgebra.opEquiv.map_sup _ _

