import Mathlib

variable (R : Type*)

variable [NonAssocSemiring R]

theorem Nat.cast_ringChar : (ringChar R : R) = 0 := by rw [ringChar.spec ringChar]

