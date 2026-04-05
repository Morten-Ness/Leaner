import Mathlib

variable {F A B C D : Type*}

variable [Mul A] [Mul B] [Mul C] [Mul D]

variable [Star A] [Star B] [Star C] [Star D]

theorem symm_bijective : Function.Bijective (symm : (A ≃⋆* B) → B ≃⋆* A) := Function.bijective_iff_has_inverse.mpr ⟨_, StarMulEquiv.symm_symm, StarMulEquiv.symm_symm⟩

