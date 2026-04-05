import Mathlib

variable {α β : Type*}

variable [Monoid α]

theorem isLeftRegular_ofDual {a : αᵒᵈ} : IsLeftRegular (ofDual a) ↔ IsLeftRegular a := .rfl

