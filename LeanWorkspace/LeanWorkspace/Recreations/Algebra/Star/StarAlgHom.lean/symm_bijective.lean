import Mathlib

variable {F R A B C : Type*} [Add A] [Add B] [Mul A] [Mul B] [SMul R A] [SMul R B] [Star A]
  [Star B] [Add C] [Mul C] [SMul R C] [Star C]

theorem symm_bijective : Function.Bijective (symm : (A ≃⋆ₐ[R] B) → B ≃⋆ₐ[R] A) := Function.bijective_iff_has_inverse.mpr ⟨_, StarAlgEquiv.symm_symm, StarAlgEquiv.symm_symm⟩

