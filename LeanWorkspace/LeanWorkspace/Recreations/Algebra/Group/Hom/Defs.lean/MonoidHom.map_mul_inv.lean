import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem map_mul_inv [Group α] [DivisionMonoid β] (f : α →* β) (g h : α) :
    f (g * h⁻¹) = f g * (f h)⁻¹ := by simp

