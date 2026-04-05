import Mathlib

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommSemiring R] [Ring A] [Algebra R A]

theorem _root_.Units.zero_notMem_spectrum (a : Aˣ) : 0 ∉ spectrum R (a : A) := spectrum.zero_notMem R a.isUnit

