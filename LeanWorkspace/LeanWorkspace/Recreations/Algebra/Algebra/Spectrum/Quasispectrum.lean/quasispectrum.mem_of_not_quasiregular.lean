import Mathlib

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

theorem quasispectrum.mem_of_not_quasiregular (a : A) {r : Rˣ}
    (hr : ¬ IsQuasiregular (-(r⁻¹ • a))) : (r : R) ∈ quasispectrum R a := fun _ ↦ by simpa using hr

