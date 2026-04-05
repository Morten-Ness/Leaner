import Mathlib

variable {ι : Sort*} {G : Type*} [Group G]

theorem op_le_iff {S₁ : Subgroup G} {S₂ : Subgroup Gᵐᵒᵖ} : S₁.op ≤ S₂ ↔ S₁ ≤ S₂.unop := MulOpposite.op_surjective.forall

