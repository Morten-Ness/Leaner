import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocSemiring R]

theorem op_le_iff {S₁ : Subsemiring R} {S₂ : Subsemiring Rᵐᵒᵖ} : S₁.op ≤ S₂ ↔ S₁ ≤ S₂.unop := MulOpposite.op_surjective.forall

