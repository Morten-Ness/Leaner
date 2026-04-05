import Mathlib

variable (M α : Type*) [Monoid M]

variable [AddGroup α] [DistribMulAction M α]

theorem FixedPoints.addSubgroup_toAddSubmonoid : (α^+M).toAddSubmonoid = addSubmonoid M α := rfl

