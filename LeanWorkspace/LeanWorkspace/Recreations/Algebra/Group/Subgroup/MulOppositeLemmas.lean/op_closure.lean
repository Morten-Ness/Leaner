import Mathlib

variable {ι : Sort*} {G : Type*} [Group G]

theorem op_closure (s : Set G) : (closure s).op = closure (MulOpposite.unop ⁻¹' s) := by
  simp_rw [closure, Subgroup.op_sInf, Set.preimage_setOf_eq, Subgroup.coe_unop]
  congr with a
  exact MulOpposite.unop_surjective.forall

