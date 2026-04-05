import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

variable [Mul M] [Mul N]

variable [FunLike F M N]

theorem map_comp_mul [MulHomClass F M N] (f : F) (g h : ι → M) : f ∘ (g * h) = f ∘ g * f ∘ h := by
  ext; simp

