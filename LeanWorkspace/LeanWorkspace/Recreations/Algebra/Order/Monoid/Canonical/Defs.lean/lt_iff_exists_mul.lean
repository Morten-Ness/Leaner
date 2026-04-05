import Mathlib

variable {α : Type u}

variable [MulOneClass α]

variable [PartialOrder α] [CanonicallyOrderedMul α] {a b c : α}

theorem lt_iff_exists_mul [MulLeftStrictMono α] : a < b ↔ ∃ c > 1, b = a * c := by
  rw [lt_iff_le_and_ne, le_iff_exists_mul, ← exists_and_right]
  apply exists_congr
  intro c
  rw [and_comm, and_congr_left_iff, gt_iff_lt]
  rintro rfl
  constructor
  · rw [one_lt_iff_ne_one]
    apply mt
    rintro rfl
    rw [mul_one]
  · rw [← (self_le_mul_right a c).lt_iff_ne]
    apply lt_mul_of_one_lt_right'

