import Mathlib

variable {F α β γ : Type*}

variable [Group α] [DivisionMonoid β] [FunLike F α β] [MonoidHomClass F α β] (m : F) {s t : Set α}

theorem image_div : m '' (s / t) = m '' s / m '' t := image_image2_distrib <| map_div m

