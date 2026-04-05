import Mathlib

variable (M : Type*) [Monoid M]

variable (G : Type*) [Group G] [Fintype G]

variable (R : Type*) [CommRing R] [MulSemiringAction G R]

theorem prodXSubSMul.monic (x : R) : (prodXSubSMul G R x).Monic := Polynomial.monic_prod_of_monic _ _ fun _ _ ↦ Polynomial.monic_X_sub_C _

