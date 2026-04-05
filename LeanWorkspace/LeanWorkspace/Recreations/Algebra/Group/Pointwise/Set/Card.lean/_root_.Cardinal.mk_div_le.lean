import Mathlib

open scoped Cardinal Pointwise

variable {G M α : Type*}

variable [DivInvMonoid M] {s t : Set M}

theorem _root_.Cardinal.mk_div_le : #(s / t) ≤ #s * #t := by
  rw [← image2_div]; exact Cardinal.mk_image2_le

