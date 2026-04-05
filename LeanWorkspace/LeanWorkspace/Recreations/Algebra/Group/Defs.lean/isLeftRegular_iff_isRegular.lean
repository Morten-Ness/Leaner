import Mathlib

variable {G : Type*}

variable [CommMagma G] {a : G}

theorem isLeftRegular_iff_isRegular : IsLeftRegular a ↔ IsRegular a := by
  simp [isRegular_iff, IsLeftRegular, IsRightRegular, mul_comm]

