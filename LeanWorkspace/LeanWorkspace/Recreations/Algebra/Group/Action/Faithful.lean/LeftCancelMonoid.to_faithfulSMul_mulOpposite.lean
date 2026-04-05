import Mathlib

variable {M G α : Type*}

theorem LeftCancelMonoid.to_faithfulSMul_mulOpposite [LeftCancelMonoid α] : FaithfulSMul αᵐᵒᵖ α := inferInstance

