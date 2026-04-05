import Mathlib

variable {ι : Sort*} {M : Type*} [Mul M]

theorem unop_le_unop_iff {S₁ S₂ : Subsemigroup Mᵐᵒᵖ} : S₁.unop ≤ S₂.unop ↔ S₁ ≤ S₂ := MulOpposite.unop_surjective.forall

