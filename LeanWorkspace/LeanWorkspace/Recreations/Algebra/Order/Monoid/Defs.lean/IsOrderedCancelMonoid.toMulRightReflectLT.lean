import Mathlib

variable {α : Type*}

variable [CommMonoid α] [PartialOrder α] [IsOrderedCancelMonoid α]

theorem IsOrderedCancelMonoid.toMulRightReflectLT :
    MulRightReflectLT α := inferInstance

-- See note [lower instance priority]

