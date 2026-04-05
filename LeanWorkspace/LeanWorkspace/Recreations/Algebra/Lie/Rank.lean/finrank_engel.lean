import Mathlib

variable {R A L M ι ιₘ : Type*}

variable [CommRing R]

variable [CommRing A] [Algebra R A]

variable [LieRing L] [LieAlgebra R L] [Module.Finite R L] [Module.Free R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [Module.Finite R M] [Module.Free R M]

variable [Fintype ι]

variable [Fintype ιₘ]

variable (b : Basis ι R L) (bₘ : Basis ιₘ R M) (x : L)

variable (K : Type*) {L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [Module.Finite K L]

theorem finrank_engel (x : L) :
    finrank K (engel K x) = (ad K L x).charpoly.natTrailingDegree := (ad K L x).finrank_maxGenEigenspace_zero_eq

