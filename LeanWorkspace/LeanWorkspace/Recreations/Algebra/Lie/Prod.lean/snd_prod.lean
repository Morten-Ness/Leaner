import Mathlib

variable {R L₁ L₂ L L₃ L₄ L₅ L₆ : Type*}
  [CommRing R] [LieRing L₁] [LieAlgebra R L₁] [LieRing L₂] [LieAlgebra R L₂]
  [LieRing L] [LieAlgebra R L] [LieRing L₃] [LieAlgebra R L₃] [LieRing L₄] [LieAlgebra R L₄]
  [LieRing L₅] [LieAlgebra R L₅] [LieRing L₆] [LieAlgebra R L₆]

theorem snd_prod (f : L →ₗ⁅R⁆ L₁) (g : L →ₗ⁅R⁆ L₂) : (LieHom.snd R L₁ L₂).comp (LieHom.prod f g) = g := rfl

