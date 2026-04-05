import Mathlib

variable {ι : Sort*} {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem op_adjoin (s : Set A) :
    (Algebra.adjoin R s).op = Algebra.adjoin R (MulOpposite.unop ⁻¹' s) := by
  apply toSubsemiring_injective
  simp_rw [Algebra.adjoin, op_toSubsemiring, Subsemiring.op_closure, Set.preimage_union]
  congr with x
  simp_rw [Set.mem_preimage, Set.mem_range, MulOpposite.algebraMap_apply]
  congr!
  rw [← MulOpposite.op_injective.eq_iff (b := x.unop), MulOpposite.op_unop]

