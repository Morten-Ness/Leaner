import Mathlib

variable {𝕜 G : Type*}

variable {α β : Type*}

variable [Zero α] [Zero β] [SMulZeroClass α β] [Preorder α] [Preorder β] [PosSMulMono α β] {a : α}
  {b : β}

theorem smul_nonneg_of_nonneg_of_pos (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a • b := smul_nonneg ha hb.le

