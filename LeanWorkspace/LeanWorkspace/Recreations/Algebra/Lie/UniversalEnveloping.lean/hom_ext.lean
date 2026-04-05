import Mathlib

variable (R : Type u₁) (L : Type u₂)

variable [CommRing R] [LieRing L] [LieAlgebra R L]

variable {A : Type u₃} [Ring A] [Algebra R A] (f : L →ₗ⁅R⁆ A)

theorem hom_ext {g₁ g₂ : UniversalEnvelopingAlgebra R L →ₐ[R] A}
    (h :
      (g₁ : UniversalEnvelopingAlgebra R L →ₗ⁅R⁆ A).comp (UniversalEnvelopingAlgebra.ι R) =
        (g₂ : UniversalEnvelopingAlgebra R L →ₗ⁅R⁆ A).comp (UniversalEnvelopingAlgebra.ι R)) :
    g₁ = g₂ := have h' : (UniversalEnvelopingAlgebra.lift R).symm g₁ = (UniversalEnvelopingAlgebra.lift R).symm g₂ := by simp [h]
  (UniversalEnvelopingAlgebra.lift R).symm.injective h'

