import Mathlib

variable {ι : Type*}

theorem up'_mk {α : Type*} [Add α] [IsRightCancelAdd α] (a : α) (i j : α) (h : i + a = j) :
    (ComplexShape.up' a).Rel i j := h

