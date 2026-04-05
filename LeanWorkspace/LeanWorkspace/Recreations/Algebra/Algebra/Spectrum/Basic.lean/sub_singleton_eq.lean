import Mathlib

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommRing R] [Ring A] [Algebra R A]

theorem sub_singleton_eq (a : A) (r : R) : σ a - {r} = σ (a - ↑ₐ r) := by
  simpa only [neg_sub, spectrum.neg_eq] using congr_arg Neg.neg (spectrum.singleton_sub_eq a r)

