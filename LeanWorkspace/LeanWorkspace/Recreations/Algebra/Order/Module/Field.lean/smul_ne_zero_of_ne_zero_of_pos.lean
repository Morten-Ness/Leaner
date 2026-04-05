import Mathlib

variable {𝕜 G : Type*}

variable {α β : Type*}

variable [Semiring α] [IsDomain α] [AddCommMonoid β] [Module α β] [Module.IsTorsionFree α β]
  {a : α} {b : β}

theorem smul_ne_zero_of_ne_zero_of_pos [Preorder β] (ha : a ≠ 0) (hb : 0 < b) : a • b ≠ 0 := smul_ne_zero ha hb.ne'

