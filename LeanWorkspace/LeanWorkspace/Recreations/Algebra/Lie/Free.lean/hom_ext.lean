import Mathlib

variable (R : Type u) (X : Type v) [CommRing R]

variable {L : Type w} [LieRing L] [LieAlgebra R L]

theorem hom_ext {F₁ F₂ : FreeLieAlgebra R X →ₗ⁅R⁆ L} (h : ∀ x, F₁ (FreeLieAlgebra.of R x) = F₂ (FreeLieAlgebra.of R x)) :
    F₁ = F₂ := have h' : (FreeLieAlgebra.lift R).symm F₁ = (FreeLieAlgebra.lift R).symm F₂ := by ext; simp [h]
  (FreeLieAlgebra.lift R).symm.injective h'

