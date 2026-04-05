import Mathlib

open scoped Pointwise

variable {R : Type*} [CommRing R]

variable {K : Type*} [Field K] [Algebra R K]

variable (K) {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

variable [IsDomain R]

variable [IsPrincipalIdealRing R]

theorem finrank_of_pi {ι : Type*} [Fintype ι] [IsFractionRing R K] (M : Submodule R (ι → K))
    [Submodule.IsLattice K M] : Module.finrank R M = Fintype.card ι := Module.finrank_eq_of_rank_eq (Submodule.IsLattice.rank_of_pi K M)

