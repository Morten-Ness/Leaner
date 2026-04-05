import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [Group α] [DivisionMonoid β] [FunLike F α β] [MonoidHomClass F α β]

variable (f : F) {s t : Finset α} {a b : α}

theorem image_div : (s / t).image (f : α → β) = s.image f / t.image f := image_image₂_distrib <| map_div f

