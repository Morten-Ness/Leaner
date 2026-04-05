import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem map_inv [Group α] [DivisionMonoid β] (f : α →* β) (a : α) : f a⁻¹ = (f a)⁻¹ := map_inv f _

