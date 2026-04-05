import Mathlib

variable (R : Type u₁) (L : Type u₂)

variable [CommRing R] [LieRing L] [LieAlgebra R L]

variable {A : Type u₃} [Ring A] [Algebra R A] (f : L →ₗ⁅R⁆ A)

theorem lift_unique (g : UniversalEnvelopingAlgebra R L →ₐ[R] A) : g ∘ UniversalEnvelopingAlgebra.ι R = f ↔ g = UniversalEnvelopingAlgebra.lift R f := by
  refine Iff.trans ?_ (UniversalEnvelopingAlgebra.lift R).symm_apply_eq
  constructor <;> · intro h; ext; simp [← h]

