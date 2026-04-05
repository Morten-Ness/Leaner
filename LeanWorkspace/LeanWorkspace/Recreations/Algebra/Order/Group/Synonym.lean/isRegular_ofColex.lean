import Mathlib

variable {α β : Type*}

variable [Monoid α]

theorem isRegular_ofColex {a : Colex α} : IsRegular (ofColex a) ↔ IsRegular a := .rfl

