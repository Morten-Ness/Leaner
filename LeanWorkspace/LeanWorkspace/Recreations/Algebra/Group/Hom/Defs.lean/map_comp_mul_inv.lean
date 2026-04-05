import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

variable [MulOne M] [MulOne N]

variable [FunLike F M N]

variable [FunLike F G H]

theorem map_comp_mul_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f : F) (g h : ι → G) :
    f ∘ (g * h⁻¹) = f ∘ g * (f ∘ h)⁻¹ := by simp

