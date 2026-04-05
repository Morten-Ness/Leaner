import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocRing R]

theorem op_le_iff {S₁ : Subring R} {S₂ : Subring Rᵐᵒᵖ} : S₁.op ≤ S₂ ↔ S₁ ≤ S₂.unop := MulOpposite.op_surjective.forall

