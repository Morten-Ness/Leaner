import Mathlib

variable {ι : Type*}

variable (c : ComplexShape ι) [c.HasNoLoop] (j : ι)

theorem hasNoLoop_up' {α : Type*} [AddZeroClass α] [IsRightCancelAdd α] [IsLeftCancelAdd α]
    (a : α) (ha : a ≠ 0) :
    (up' a).HasNoLoop where
  ComplexShape.not_rel_self i (hi : _ = _) := ha (add_left_cancel (by rw [add_zero, hi]))

