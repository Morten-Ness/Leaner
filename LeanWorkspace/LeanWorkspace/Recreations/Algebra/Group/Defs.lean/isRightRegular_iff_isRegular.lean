import Mathlib

variable {G : Type*}

variable [CommMagma G] {a : G}

theorem isRightRegular_iff_isRegular : IsRightRegular a ↔ IsRegular a := by
  simp [isRegular_iff, IsLeftRegular, IsRightRegular, mul_comm]

