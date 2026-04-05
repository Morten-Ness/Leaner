import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

variable [MulOne M] [MulOne N]

variable [FunLike F M N]

variable [FunLike F G H]

theorem map_comp_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f : F) (g : ι → G) :
    f ∘ g⁻¹ = (f ∘ g)⁻¹ := by ext; simp

