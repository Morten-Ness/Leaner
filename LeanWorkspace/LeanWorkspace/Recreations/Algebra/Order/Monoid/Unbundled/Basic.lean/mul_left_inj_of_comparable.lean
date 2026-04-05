import Mathlib

variable {α β : Type*}

variable [Mul α]

variable [PartialOrder α]

theorem mul_left_inj_of_comparable [MulRightStrictMono α] {a b c : α} (h : b ≤ c ∨ c ≤ b) :
    c * a = b * a ↔ c = b := by
  refine ⟨fun h' => ?_, (· ▸ rfl)⟩
  contrapose h'
  obtain h | h := h
  · exact mul_lt_mul_left (h.lt_of_ne' h') a |>.ne'
  · exact mul_lt_mul_left (h.lt_of_ne h') a |>.ne

