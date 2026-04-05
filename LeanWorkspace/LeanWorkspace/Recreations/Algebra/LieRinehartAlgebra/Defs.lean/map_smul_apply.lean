import Mathlib

variable {R A₁ L₁ A₂ L₂ A₃ L₃ : Type*} [CommRing R]
  [CommRing A₁] [LieRing L₁] [Module A₁ L₁] [LieRingModule L₁ A₁]
  [CommRing A₂] [LieRing L₂] [Module A₂ L₂] [LieRingModule L₂ A₂]
  [CommRing A₃] [LieRing L₃] [Module A₃ L₃] [LieRingModule L₃ A₃]
  [Algebra R A₁] [LieAlgebra R L₁] [Algebra R A₂] [LieAlgebra R L₂]
  [Algebra R A₃] [LieAlgebra R L₃]
  {σ₁₂ : A₁ →ₐ[R] A₂} {σ₂₃ : A₂ →ₐ[R] A₃}

theorem map_smul_apply (f : L₁ →ₗ⁅σ₁₂⁆ L₂) (a : A₁) (x : L₁) :
    f (a • x) = σ₁₂ a • f x := f.map_smul_apply' a x

