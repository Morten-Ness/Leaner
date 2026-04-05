import Mathlib

variable (R : Type u₁) (L : Type u₂)

variable [CommRing R] [LieRing L] [LieAlgebra R L]

variable {A : Type u₃} [Ring A] [Algebra R A] (f : L →ₗ⁅R⁆ A)

theorem lift_ι_apply (x : L) : UniversalEnvelopingAlgebra.lift R f (UniversalEnvelopingAlgebra.ι R x) = f x := by
  rw [← Function.comp_apply (f := UniversalEnvelopingAlgebra.lift R f) (g := UniversalEnvelopingAlgebra.ι R) (x := x), UniversalEnvelopingAlgebra.ι_comp_lift]

