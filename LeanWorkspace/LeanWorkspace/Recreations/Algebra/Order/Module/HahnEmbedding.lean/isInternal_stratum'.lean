import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable [Module K M] [IsOrderedModule K M]

variable {R : Type*} [AddCommGroup R] [LinearOrder R]

variable [Module K R]

variable (u : ArchimedeanStrata K M) {c : FiniteArchimedeanClass M}

theorem isInternal_stratum' : DirectSum.IsInternal u.stratum' := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top HahnEmbedding.ArchimedeanStrata.iSupIndep_stratum' u
  apply Submodule.map_injective_of_injective u.baseDomain.subtype_injective
  suffices ⨆ i, u.baseDomain ⊓ u.stratum i = u.baseDomain by simpa using this
  apply iSup_congr
  intro c
  simpa using le_iSup _ _

noncomputable

