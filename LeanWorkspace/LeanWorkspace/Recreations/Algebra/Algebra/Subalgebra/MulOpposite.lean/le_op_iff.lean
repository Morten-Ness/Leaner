import Mathlib

variable {ι : Sort*} {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem le_op_iff {S₁ : Subalgebra R Aᵐᵒᵖ} {S₂ : Subalgebra R A} : S₁ ≤ S₂.op ↔ S₁.unop ≤ S₂ := MulOpposite.op_surjective.forall

