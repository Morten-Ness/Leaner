import Mathlib

variable {α β : Type*}

variable [Monoid α]

theorem isRegular_ofDual {a : αᵒᵈ} : IsRegular (ofDual a) ↔ IsRegular a := .rfl

