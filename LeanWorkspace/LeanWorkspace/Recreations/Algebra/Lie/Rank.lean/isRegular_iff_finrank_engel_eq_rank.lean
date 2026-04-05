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

theorem isRegular_iff_finrank_engel_eq_rank (x : L) :
    LieModule.IsRegular K x ↔ finrank K (engel K x) = LieModule.rank K L := by
  rw [LieAlgebra.isRegular_iff_natTrailingDegree_charpoly_eq_rank, LieAlgebra.finrank_engel]

