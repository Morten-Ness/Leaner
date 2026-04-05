import Mathlib

variable {α β : Type*}

variable [Mul α]

variable [Preorder α]

theorem mul_left_strictMono [MulRightStrictMono α] {a : α} : StrictMono (· * a) := fun _ _ h ↦ mul_lt_mul_left h _

-- Note: in this section, we use `@[gcongr high]` so that these lemmas have a higher priority than
-- lemmas like `mul_le_mul_of_nonneg`, which have an extra side condition.

