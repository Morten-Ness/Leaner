import Mathlib

variable {ι : Sort*} {M : Type*} [MulOneClass M]

theorem le_op_iff {S₁ : Submonoid Mᵐᵒᵖ} {S₂ : Submonoid M} : S₁ ≤ S₂.op ↔ S₁.unop ≤ S₂ := MulOpposite.op_surjective.forall

