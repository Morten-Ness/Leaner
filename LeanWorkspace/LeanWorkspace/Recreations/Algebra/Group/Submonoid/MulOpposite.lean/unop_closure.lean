import Mathlib

variable {ι : Sort*} {M : Type*} [MulOneClass M]

theorem unop_closure (s : Set Mᵐᵒᵖ) : (closure s).unop = closure (MulOpposite.op ⁻¹' s) := by
  rw [← Submonoid.op_inj, Submonoid.op_unop, Submonoid.op_closure]
  simp_rw [Set.preimage_preimage, MulOpposite.op_unop, Set.preimage_id']

