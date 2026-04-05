import Mathlib

variable {α β : Type*}

variable [Monoid α]

theorem isLeftRegular_ofColex {a : Colex α} : IsLeftRegular (ofColex a) ↔ IsLeftRegular a := .rfl

