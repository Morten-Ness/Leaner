import Mathlib

variable {ι : Sort*} {M : Type*} [MulOneClass M]

theorem op_closure (s : Set M) : (closure s).op = closure (MulOpposite.unop ⁻¹' s) := by
  simp_rw [closure, Submonoid.op_sInf, Set.preimage_setOf_eq, Submonoid.coe_unop]
  congr with a
  exact MulOpposite.unop_surjective.forall

