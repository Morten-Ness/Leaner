import Mathlib

open scoped Pointwise

variable {R : Type*} [CommRing R]

variable {K : Type*} [Field K] [Algebra R K]

variable (K) {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

variable [IsDomain R]

theorem of_rank_le [Module.Finite K V] [IsFractionRing R K] {M : Submodule R V}
    (hfg : M.FG) (hr : Module.rank K V ≤ Module.rank R M) : Submodule.IsLattice K M where
  fg := hfg
  span_eq_top := by
    simpa using Submodule.span_range_eq_top_of_injective_of_rank_le M.injective_subtype hr

