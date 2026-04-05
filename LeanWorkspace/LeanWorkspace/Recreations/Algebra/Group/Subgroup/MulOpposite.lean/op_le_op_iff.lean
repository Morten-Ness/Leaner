import Mathlib

variable {ι : Sort*} {G : Type*} [Group G]

theorem op_le_op_iff {S₁ S₂ : Subgroup G} : S₁.op ≤ S₂.op ↔ S₁ ≤ S₂ := MulOpposite.op_surjective.forall

