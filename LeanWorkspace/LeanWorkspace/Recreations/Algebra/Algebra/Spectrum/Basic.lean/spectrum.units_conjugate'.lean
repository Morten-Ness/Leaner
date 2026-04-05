import Mathlib

open scoped Pointwise Ring

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]

theorem spectrum.units_conjugate' {a : A} {u : Aˣ} :
    spectrum R (u⁻¹ * a * u) = spectrum R a := by
  simpa using spectrum.units_conjugate (u := u⁻¹)

