import Mathlib

variable {α β : Type*}

variable [Monoid α]

theorem isRightRegular_ofColex {a : Colex α} : IsRightRegular (ofColex a) ↔ IsRightRegular a := .rfl

