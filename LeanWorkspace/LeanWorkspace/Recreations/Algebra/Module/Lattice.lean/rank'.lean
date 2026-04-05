import Mathlib

open scoped Pointwise

variable {R : Type*} [CommRing R]

variable {K : Type*} [Field K] [Algebra R K]

variable (K) {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

variable [IsDomain R]

variable [IsPrincipalIdealRing R]

theorem rank' [IsFractionRing R K] (M : Submodule R V) [Submodule.IsLattice K M] :
    Module.rank R M = Module.rank K V := by
  let b := Module.Free.chooseBasis R M
  rw [rank_eq_card_basis b, ← rank_eq_card_basis (b.extendOfIsLattice K)]

