import Mathlib

variable {α β : Type*}

variable [Monoid α]

theorem isRightRegular_ofDual {a : αᵒᵈ} : IsRightRegular (ofDual a) ↔ IsRightRegular a := .rfl

