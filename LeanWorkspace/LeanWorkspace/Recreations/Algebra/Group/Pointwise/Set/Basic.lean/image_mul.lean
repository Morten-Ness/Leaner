import Mathlib

variable {F α β γ : Type*}

variable [Mul α] [Mul β] [FunLike F α β] [MulHomClass F α β] (m : F) {s t : Set α}

theorem image_mul : m '' (s * t) = m '' s * m '' t := image_image2_distrib <| map_mul m

