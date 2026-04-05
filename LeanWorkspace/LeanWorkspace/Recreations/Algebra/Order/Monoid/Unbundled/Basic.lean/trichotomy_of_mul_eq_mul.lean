import Mathlib

variable {α β : Type*}

variable [Mul α]

variable [LinearOrder α] {a b c d : α}

theorem trichotomy_of_mul_eq_mul
    [MulLeftStrictMono α] [MulRightStrictMono α]
    (h : a * b = c * d) : (a = c ∧ b = d) ∨ a < c ∨ b < d := by
  obtain hac | rfl | hca := lt_trichotomy a c
  · grind
  · left; simpa using mul_right_inj_of_comparable (le_total d b) |>.1 h
  · obtain hbd | rfl | hdb := lt_trichotomy b d
    · grind
    · exact False.elim <| ne_of_lt (mul_lt_mul_left hca b) h.symm
    · exact False.elim <| ne_of_lt (mul_lt_mul_of_lt_of_lt hca hdb) h.symm

