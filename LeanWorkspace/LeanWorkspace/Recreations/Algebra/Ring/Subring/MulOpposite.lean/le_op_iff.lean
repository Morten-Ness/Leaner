import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocRing R]

theorem le_op_iff {S₁ : Subring Rᵐᵒᵖ} {S₂ : Subring R} : S₁ ≤ S₂.op ↔ S₁.unop ≤ S₂ := MulOpposite.op_surjective.forall

