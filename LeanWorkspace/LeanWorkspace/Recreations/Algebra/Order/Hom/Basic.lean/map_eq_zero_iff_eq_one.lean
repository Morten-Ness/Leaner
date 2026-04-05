import Mathlib

variable {ι F α β γ δ : Type*}

variable [FunLike F α β]

variable [Group α] [AddCommMonoid β] [PartialOrder β] [GroupNormClass F α β] (f : F) {x : α}

theorem map_eq_zero_iff_eq_one : f x = 0 ↔ x = 1 := ⟨eq_one_of_map_eq_zero _, by
    rintro rfl
    exact map_one_eq_zero _⟩

