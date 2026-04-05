import Mathlib

open scoped Pointwise

variable {α β : Type*}

variable [Monoid α] [AddGroup β] [DistribMulAction α β] (a : α) (s : Set α) (t : Set β)

theorem smul_set_neg : a • -t = -(a • t) := by
  simp_rw [← image_smul, ← image_neg_eq_neg, image_image, smul_neg]

