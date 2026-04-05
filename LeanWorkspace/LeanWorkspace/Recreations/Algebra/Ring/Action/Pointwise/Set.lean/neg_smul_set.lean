import Mathlib

open scoped Pointwise

variable {α β : Type*}

variable [Ring α] [AddCommGroup β] [Module α β] (a : α) (s : Set α) (t : Set β)

theorem neg_smul_set : -a • t = -(a • t) := by
  simp_rw [← image_smul, ← image_neg_eq_neg, image_image, neg_smul]

