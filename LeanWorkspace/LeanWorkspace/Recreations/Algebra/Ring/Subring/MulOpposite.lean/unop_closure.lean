import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocRing R]

theorem unop_closure (s : Set Rᵐᵒᵖ) : (closure s).unop = closure (MulOpposite.op ⁻¹' s) := by
  rw [← op_inj, Subring.op_unop, Subring.op_closure]
  simp_rw [Set.preimage_preimage, MulOpposite.op_unop, Set.preimage_id']

