import Mathlib

variable {ι : Sort*} {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem unop_le_unop_iff {S₁ S₂ : Subalgebra R Aᵐᵒᵖ} : S₁.unop ≤ S₂.unop ↔ S₁ ≤ S₂ := MulOpposite.unop_surjective.forall

