import Mathlib

variable {ι : Type*}

variable (c : ComplexShape ι) [c.HasNoLoop] (j : ι)

theorem hasNoLoop_up {α : Type*} [AddZeroClass α] [IsRightCancelAdd α] [IsLeftCancelAdd α]
    [One α] (ha : (1 : α) ≠ 0) :
    (up α).HasNoLoop := ComplexShape.hasNoLoop_up' _ ha

