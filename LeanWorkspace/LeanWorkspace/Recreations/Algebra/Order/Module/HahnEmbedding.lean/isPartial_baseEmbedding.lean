import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable [Module K M] [IsOrderedModule K M]

variable {R : Type*} [AddCommGroup R] [LinearOrder R]

variable [Module K R]

variable (seed : Seed K M R)

theorem isPartial_baseEmbedding [IsOrderedAddMonoid R] : IsPartial seed seed.baseEmbedding where
  strictMono := HahnEmbedding.Seed.baseEmbedding_strictMono seed
  baseEmbedding_le := le_refl _
  truncLT_mem_range := HahnEmbedding.Seed.truncLT_mem_range_baseEmbedding seed

