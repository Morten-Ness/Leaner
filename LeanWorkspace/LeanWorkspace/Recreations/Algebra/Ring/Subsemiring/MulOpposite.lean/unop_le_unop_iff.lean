import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocSemiring R]

theorem unop_le_unop_iff {S₁ S₂ : Subsemiring Rᵐᵒᵖ} : S₁.unop ≤ S₂.unop ↔ S₁ ≤ S₂ := MulOpposite.unop_surjective.forall

