import Mathlib

variable {α : Type*}

theorem IsRightCancelMulZero.faithfulSMul [MonoidWithZero α] [IsRightCancelMulZero α] :
    FaithfulSMul α α := inferInstance

