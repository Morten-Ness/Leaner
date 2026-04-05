import Mathlib

variable {F α β γ : Type*}

variable [Group α] {s t : Set α} {a b : α}

theorem image_inv [DivisionMonoid β] [FunLike F α β] [MonoidHomClass F α β] (f : F) (s : Set α) :
    f '' s⁻¹ = (f '' s)⁻¹ := by
  rw [← Set.image_inv_eq_inv, ← Set.image_inv_eq_inv]; exact image_comm (map_inv _)

