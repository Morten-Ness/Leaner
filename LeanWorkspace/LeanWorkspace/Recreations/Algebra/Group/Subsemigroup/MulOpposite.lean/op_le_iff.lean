import Mathlib

variable {ι : Sort*} {M : Type*} [Mul M]

theorem op_le_iff {S₁ : Subsemigroup M} {S₂ : Subsemigroup Mᵐᵒᵖ} : S₁.op ≤ S₂ ↔ S₁ ≤ S₂.unop := MulOpposite.op_surjective.forall

