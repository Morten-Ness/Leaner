import Mathlib

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommRing R] [Ring A] [Algebra R A]

theorem vadd_eq (a : A) (r : R) : r +ᵥ σ a = σ (↑ₐ r + a) := singleton_add.symm.trans <| spectrum.singleton_add_eq a r

