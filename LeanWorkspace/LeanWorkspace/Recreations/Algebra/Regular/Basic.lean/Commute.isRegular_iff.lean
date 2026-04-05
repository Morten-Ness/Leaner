import Mathlib

variable {R : Type*}

variable [Mul R]

theorem Commute.isRegular_iff {a : R} (ca : ∀ b, Commute a b) : IsRegular a ↔ IsLeftRegular a := ⟨fun h => h.left, fun h => ⟨h, h.right_of_commute ca⟩⟩

