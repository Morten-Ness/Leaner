import Mathlib

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommSemiring R] [Ring A] [Algebra R A]

theorem units_smul_resolvent_self {r : Rˣ} {a : A} :
    r • resolvent a (r : R) = resolvent (r⁻¹ • a) (1 : R) := by
  simpa only [Units.smul_def, smul_eq_mul, Units.inv_mul] using
    @spectrum.units_smul_resolvent _ _ _ _ _ r r a

