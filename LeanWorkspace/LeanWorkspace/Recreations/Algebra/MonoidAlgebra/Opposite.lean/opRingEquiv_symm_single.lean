import Mathlib

variable {R M : Type*} [Semiring R] [Mul M]

set_option backward.isDefEq.respectTransparency false in
theorem opRingEquiv_symm_single (r : Rᵐᵒᵖ) (x : Mᵐᵒᵖ) :
    MonoidAlgebra.opRingEquiv.symm (single x r) = op (single x.unop r.unop) := by simp

