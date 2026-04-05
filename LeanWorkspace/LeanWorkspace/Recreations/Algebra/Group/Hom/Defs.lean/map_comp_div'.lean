import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

variable [MulOne M] [MulOne N]

variable [FunLike F M N]

variable [FunLike F G H]

theorem map_comp_div' [DivInvMonoid G] [DivInvMonoid H] [MulHomClass F G H] (f : F)
    (hf : ∀ a, f a⁻¹ = (f a)⁻¹) (g h : ι → G) : f ∘ (g / h) = f ∘ g / f ∘ h := by
  ext; simp [map_div' f hf]

