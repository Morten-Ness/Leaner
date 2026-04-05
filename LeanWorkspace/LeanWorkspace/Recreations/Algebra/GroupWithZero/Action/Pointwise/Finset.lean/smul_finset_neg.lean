import Mathlib

open scoped Pointwise

variable {α β : Type*} [DecidableEq β]

variable [Monoid α] [AddGroup β] [DistribMulAction α β]

theorem smul_finset_neg (a : α) (t : Finset β) : a • -t = -(a • t) := by
  simp only [← image_smul, ← image_neg_eq_neg, Function.comp_def, image_image, smul_neg]

