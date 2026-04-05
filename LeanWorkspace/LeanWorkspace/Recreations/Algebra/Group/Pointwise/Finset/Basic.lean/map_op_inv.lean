import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [Inv α] {s t : Finset α} {a : α}

theorem map_op_inv (s : Finset α) : s⁻¹.map opEquiv.toEmbedding = (s.map opEquiv.toEmbedding)⁻¹ := by
  simp [map_eq_image, image_op_inv]

