import Mathlib

variable {R : Type*}

theorem Prime.squarefree [CommMonoidWithZero R] [IsCancelMulZero R] {x : R} (h : Prime x) :
    Squarefree x := h.irreducible.squarefree

