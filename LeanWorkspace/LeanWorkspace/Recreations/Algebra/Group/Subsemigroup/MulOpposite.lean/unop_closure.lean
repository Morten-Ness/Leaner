import Mathlib

variable {ι : Sort*} {M : Type*} [Mul M]

theorem unop_closure (s : Set Mᵐᵒᵖ) : (closure s).unop = closure (MulOpposite.op ⁻¹' s) := by
  rw [← Subsemigroup.op_inj, Subsemigroup.op_unop, Subsemigroup.op_closure]
  simp_rw [Set.preimage_preimage, MulOpposite.op_unop, Set.preimage_id']

