import Mathlib

variable {ι : Sort*} {M : Type*} [Mul M]

theorem le_op_iff {S₁ : Subsemigroup Mᵐᵒᵖ} {S₂ : Subsemigroup M} : S₁ ≤ S₂.op ↔ S₁.unop ≤ S₂ := MulOpposite.op_surjective.forall

