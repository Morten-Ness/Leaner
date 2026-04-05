import Mathlib

variable (R : Type u₁) (L : Type u₂)

variable [CommRing R] [LieRing L] [LieAlgebra R L]

variable {A : Type u₃} [Ring A] [Algebra R A] (f : L →ₗ⁅R⁆ A)

theorem lift_ι_apply' (x : L) :
    UniversalEnvelopingAlgebra.lift R f ((UniversalEnvelopingAlgebra.mkAlgHom R L) (ιₜ x)) = f x := by
  simpa using UniversalEnvelopingAlgebra.lift_ι_apply R f x

