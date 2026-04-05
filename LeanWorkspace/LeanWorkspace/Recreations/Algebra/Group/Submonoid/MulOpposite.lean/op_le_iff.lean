import Mathlib

variable {ι : Sort*} {M : Type*} [MulOneClass M]

theorem op_le_iff {S₁ : Submonoid M} {S₂ : Submonoid Mᵐᵒᵖ} : S₁.op ≤ S₂ ↔ S₁ ≤ S₂.unop := MulOpposite.op_surjective.forall

