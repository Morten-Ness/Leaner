import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable [Module K M] [IsOrderedModule K M]

variable {R : Type*} [AddCommGroup R] [LinearOrder R]

variable [Module K R]

variable (u : ArchimedeanStrata K M) {c : FiniteArchimedeanClass M}

theorem iSupIndep_stratum' : iSupIndep u.stratum' := by
  apply (iSupIndep_map_orderIso_iff (Submodule.mapIic u.baseDomain)).mp
  apply iSupIndep.of_coe_Iic_comp
  convert HahnEmbedding.ArchimedeanStrata.iSupIndep_stratum u
  ext1 c
  simpa using le_iSup _ _

