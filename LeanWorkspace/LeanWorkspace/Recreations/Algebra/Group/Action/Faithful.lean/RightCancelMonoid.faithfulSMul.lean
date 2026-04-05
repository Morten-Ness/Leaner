import Mathlib

variable {M G α : Type*}

theorem RightCancelMonoid.faithfulSMul [RightCancelMonoid α] : FaithfulSMul α α := inferInstance

