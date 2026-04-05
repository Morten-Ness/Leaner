import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [Group α] [DivisionMonoid β] [FunLike F α β] [MonoidHomClass F α β]

variable (f : F) {s t : Finset α} {a b : α}

theorem image_inv (f : F) (s : Finset α) : s⁻¹.image f = (s.image f)⁻¹ := image_comm (map_inv _)

