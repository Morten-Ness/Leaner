import Mathlib

variable {F α β : Type*}

variable [Mul α]

theorem isSquare_iff_exists_mul_self (a : α) : IsSquare a ↔ ∃ r, a = r * r := .rfl

alias ⟨IsSquare.exists_mul_self, _⟩ := isSquare_iff_exists_mul_self
attribute [to_additive (attr := aesop unsafe 5% forward)] IsSquare.exists_mul_self

