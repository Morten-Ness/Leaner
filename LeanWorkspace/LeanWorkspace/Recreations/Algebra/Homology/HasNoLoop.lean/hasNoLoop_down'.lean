import Mathlib

variable {ι : Type*}

variable (c : ComplexShape ι) [c.HasNoLoop] (j : ι)

theorem hasNoLoop_down' {α : Type*} [AddZeroClass α] [IsRightCancelAdd α] [IsLeftCancelAdd α]
    (a : α) (ha : a ≠ 0) :
    (down' a).HasNoLoop := by
  have := ComplexShape.hasNoLoop_up' a ha
  exact inferInstanceAs (up' a).symm.HasNoLoop

