import Mathlib

variable {R L₁ L₂ L L₃ L₄ L₅ L₆ : Type*}
  [CommRing R] [LieRing L₁] [LieAlgebra R L₁] [LieRing L₂] [LieAlgebra R L₂]
  [LieRing L] [LieAlgebra R L] [LieRing L₃] [LieAlgebra R L₃] [LieRing L₄] [LieAlgebra R L₄]
  [LieRing L₅] [LieAlgebra R L₅] [LieRing L₆] [LieAlgebra R L₆]

theorem prodMap_comp (f₁₂ : L₁ →ₗ⁅R⁆ L₂) (f₂₃ : L₂ →ₗ⁅R⁆ L₃) (g₁₂ : L₄ →ₗ⁅R⁆ L₅)
    (g₂₃ : L₅ →ₗ⁅R⁆ L₆) :
    (f₂₃.prodMap g₂₃).comp (f₁₂.prodMap g₁₂) = (f₂₃.comp f₁₂).prodMap (g₂₃.comp g₁₂) := rfl

