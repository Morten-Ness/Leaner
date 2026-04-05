import Mathlib

variable (R K L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L] [IsDomain R]

theorem isLieAbelian_of_ker_traceForm_eq_bot [Module.Free R M] [Module.Finite R M]
    (h : LinearMap.ker (LieModule.traceForm R L M) = ⊥) : IsLieAbelian L := by
  simpa only [← disjoint_lowerCentralSeries_maxTrivSubmodule_iff R L L, disjoint_iff_inf_le,
    LieIdeal.toLieSubalgebra_toSubmodule, LieSubmodule.toSubmodule_eq_bot, h]
    using LieModule.lowerCentralSeries_one_inf_center_le_ker_traceForm R L M

