import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocSemiring R]

theorem le_op_iff {S₁ : Subsemiring Rᵐᵒᵖ} {S₂ : Subsemiring R} : S₁ ≤ S₂.op ↔ S₁.unop ≤ S₂ := MulOpposite.op_surjective.forall

