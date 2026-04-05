import Mathlib

variable {ι : Sort*} {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem unop_adjoin (s : Set Aᵐᵒᵖ) :
    (Algebra.adjoin R s).unop = Algebra.adjoin R (MulOpposite.op ⁻¹' s) := by
  apply toSubsemiring_injective
  simp_rw [Algebra.adjoin, unop_toSubsemiring, Subsemiring.unop_closure, Set.preimage_union]
  congr with x
  simp

