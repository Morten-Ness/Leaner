import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocRing R]

theorem op_closure (s : Set R) : (closure s).op = closure (MulOpposite.unop ⁻¹' s) := by
  simp_rw [closure, Subring.op_sInf, Set.preimage_setOf_eq, coe_unop]
  congr with a
  exact MulOpposite.unop_surjective.forall

