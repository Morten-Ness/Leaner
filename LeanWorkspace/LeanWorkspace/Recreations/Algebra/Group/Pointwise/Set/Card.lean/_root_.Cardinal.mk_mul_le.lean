import Mathlib

open scoped Cardinal Pointwise

variable {G M α : Type*}

variable [Mul M] {s t : Set M}

theorem _root_.Cardinal.mk_mul_le : #(s * t) ≤ #s * #t := by
  rw [← image2_mul]; exact Cardinal.mk_image2_le

