import Mathlib

variable {R : Type*} [Semiring R] [LinearOrder R] [IsStrictOrderedRing R] {a : R}

theorem invOf_pos [Invertible a] : 0 < ⅟a ↔ 0 < a := haveI : 0 < a * ⅟a := by simp only [mul_invOf_self, zero_lt_one]
  ⟨fun h => pos_of_mul_pos_left this h.le, fun h => pos_of_mul_pos_right this h.le⟩

