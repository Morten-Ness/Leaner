import Mathlib

open scoped Pointwise

variable {R : Type*} [CommRing R]

variable {K : Type*} [Field K] [Algebra R K]

variable (K) {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

variable [IsDomain R]

variable [IsPrincipalIdealRing R]

theorem rank_of_pi {ι : Type*} [Fintype ι] [IsFractionRing R K] (M : Submodule R (ι → K))
    [Submodule.IsLattice K M] : Module.rank R M = Fintype.card ι := by
  rw [Submodule.IsLattice.rank' K M]
  simp

