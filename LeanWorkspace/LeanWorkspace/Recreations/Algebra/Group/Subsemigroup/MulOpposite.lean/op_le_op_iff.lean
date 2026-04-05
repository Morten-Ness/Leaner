import Mathlib

variable {ι : Sort*} {M : Type*} [Mul M]

theorem op_le_op_iff {S₁ S₂ : Subsemigroup M} : S₁.op ≤ S₂.op ↔ S₁ ≤ S₂ := MulOpposite.op_surjective.forall

