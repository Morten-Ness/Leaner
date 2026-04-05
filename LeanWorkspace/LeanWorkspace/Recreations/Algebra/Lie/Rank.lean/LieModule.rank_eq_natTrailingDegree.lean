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

theorem rank_eq_natTrailingDegree [Nontrivial R] [DecidableEq ι] :
    LieModule.rank R L M = (polyCharpoly φ b).natTrailingDegree := by
  apply nilRank_eq_polyCharpoly_natTrailingDegree

