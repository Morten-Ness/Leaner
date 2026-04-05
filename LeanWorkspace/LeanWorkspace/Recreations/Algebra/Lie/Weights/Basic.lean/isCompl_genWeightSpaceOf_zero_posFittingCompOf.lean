import Mathlib

variable {K R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

variable [IsNoetherian R M] [IsArtinian R M]

theorem isCompl_genWeightSpaceOf_zero_posFittingCompOf (x : L) :
    IsCompl (LieModule.genWeightSpaceOf M 0 x) (LieModule.posFittingCompOf R M x) := by
  simpa only [isCompl_iff, codisjoint_iff, disjoint_iff, ← LieSubmodule.toSubmodule_inj,
    LieSubmodule.sup_toSubmodule, LieSubmodule.inf_toSubmodule,
    LieSubmodule.top_toSubmodule, LieSubmodule.bot_toSubmodule, LieModule.coe_genWeightSpaceOf_zero] using
    (toEnd R L M x).isCompl_iSup_ker_pow_iInf_range_pow

