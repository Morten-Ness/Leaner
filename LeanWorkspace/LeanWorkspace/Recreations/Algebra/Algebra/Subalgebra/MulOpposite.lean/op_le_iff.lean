import Mathlib

variable {ι : Sort*} {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem op_le_iff {S₁ : Subalgebra R A} {S₂ : Subalgebra R Aᵐᵒᵖ} : S₁.op ≤ S₂ ↔ S₁ ≤ S₂.unop := MulOpposite.op_surjective.forall

