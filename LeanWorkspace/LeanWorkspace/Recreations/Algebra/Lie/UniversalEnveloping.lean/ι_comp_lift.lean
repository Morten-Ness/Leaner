import Mathlib

variable (R : Type u₁) (L : Type u₂)

variable [CommRing R] [LieRing L] [LieAlgebra R L]

variable {A : Type u₃} [Ring A] [Algebra R A] (f : L →ₗ⁅R⁆ A)

theorem ι_comp_lift : UniversalEnvelopingAlgebra.lift R f ∘ UniversalEnvelopingAlgebra.ι R = f := funext <| LieHom.ext_iff.mp <| (UniversalEnvelopingAlgebra.lift R).symm_apply_apply f

-- `simp`-normal form is `lift_ι_apply'`.

