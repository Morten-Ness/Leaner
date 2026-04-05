import Mathlib

variable {ι : Type*}

theorem up_mk {α : Type*} [Add α] [IsRightCancelAdd α] [One α] (i j : α) (h : i + 1 = j) :
    (ComplexShape.up α).Rel i j := ComplexShape.up'_mk (1 : α) i j h

