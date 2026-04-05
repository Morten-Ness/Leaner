import Mathlib

variable {ι : Sort*} {M : Type*} [MulOneClass M]

theorem op_le_op_iff {S₁ S₂ : Submonoid M} : S₁.op ≤ S₂.op ↔ S₁ ≤ S₂ := MulOpposite.op_surjective.forall

