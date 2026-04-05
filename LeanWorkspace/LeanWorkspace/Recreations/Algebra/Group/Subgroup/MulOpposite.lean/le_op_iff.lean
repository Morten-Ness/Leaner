import Mathlib

variable {ι : Sort*} {G : Type*} [Group G]

theorem le_op_iff {S₁ : Subgroup Gᵐᵒᵖ} {S₂ : Subgroup G} : S₁ ≤ S₂.op ↔ S₁.unop ≤ S₂ := MulOpposite.op_surjective.forall

