import Mathlib

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem mem_spectrum_inr_of_not_isUnit {R A : Type*} [CommRing R]
    [NonUnitalRing A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    (a : A) (r : R) (hr : ¬ IsUnit r) : r ∈ spectrum R (a : Unitization R A) := fun h ↦ hr <| by simpa [map_sub] using h.map (fstHom R A)

