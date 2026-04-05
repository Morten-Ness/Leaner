import Mathlib

variable {ι : Sort*} {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem op_le_op_iff {S₁ S₂ : Subalgebra R A} : S₁.op ≤ S₂.op ↔ S₁ ≤ S₂ := MulOpposite.op_surjective.forall

