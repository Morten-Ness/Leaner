import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable [Module K M] [IsOrderedModule K M]

variable {R : Type*} [AddCommGroup R] [LinearOrder R]

variable [Module K R]

variable (seed : Seed K M R)

set_option backward.isDefEq.respectTransparency false in
theorem mem_domain_baseEmbedding {x : M} {c : FiniteArchimedeanClass M} (h : x ∈ seed.stratum c) :
    x ∈ seed.baseEmbedding.domain := by
  apply Set.mem_of_mem_of_subset h
  rw [HahnEmbedding.Seed.domain_baseEmbedding]
  simpa using le_iSup_iff.mpr fun _ h ↦ h c

