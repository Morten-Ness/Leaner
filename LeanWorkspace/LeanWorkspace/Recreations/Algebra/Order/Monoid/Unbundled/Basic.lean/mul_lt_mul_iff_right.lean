import Mathlib

variable {α β : Type*}

variable [Mul α]

variable [LT α]

theorem mul_lt_mul_iff_right [MulRightStrictMono α]
    [MulRightReflectLT α] (a : α) {b c : α} :
    b * a < c * a ↔ b < c := rel_iff_cov α α (swap (· * ·)) (· < ·) a

-- Note: in this section, we use `@[gcongr high]` so that these lemmas have a higher priority than
-- lemmas like `mul_lt_mul_of_pos_left`, which have an extra side condition.

