import Mathlib

variable {ι : Sort*} {M : Type*} [Mul M]

theorem unop_iInf (S : ι → Subsemigroup Mᵐᵒᵖ) : (iInf S).unop = ⨅ i, (S i).unop := by
  ext x
  simp [Subsemigroup.mem_iInf]
