import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocRing R]

theorem op_le_op_iff {S₁ S₂ : Subring R} : S₁.op ≤ S₂.op ↔ S₁ ≤ S₂ := MulOpposite.op_surjective.forall

