import Mathlib

variable {ι : Sort*} {M : Type*} [MulOneClass M]

theorem unop_le_unop_iff {S₁ S₂ : Submonoid Mᵐᵒᵖ} : S₁.unop ≤ S₂.unop ↔ S₁ ≤ S₂ := MulOpposite.unop_surjective.forall

