import Mathlib

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  {M : Type*} [AddCommGroup M] [Module R M] (N : Submodule R M)

variable [IsLocalRing R]

theorem spanFinrank_maximalIdeal_eq_finrank_cotangentSpace_of_fg (fg : (maximalIdeal R).FG) :
    (maximalIdeal R).spanFinrank = Module.finrank (ResidueField R) (CotangentSpace R) := IsLocalRing.spanFinrank_eq_finrank_quotient _ fg

