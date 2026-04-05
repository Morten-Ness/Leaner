import Mathlib

variable {𝕜 G : Type*}

variable {α β : Type*}

variable [Semiring α] [IsDomain α] [AddCommMonoid β] [Module α β] [Module.IsTorsionFree α β]
  {a : α} {b : β}

theorem smul_ne_zero_of_pos_of_ne_zero [Preorder α] (ha : 0 < a) (hb : b ≠ 0) : a • b ≠ 0 := smul_ne_zero ha.ne' hb

