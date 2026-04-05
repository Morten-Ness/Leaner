import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable [Module K M] [IsOrderedModule K M]

variable {R : Type*} [AddCommGroup R] [LinearOrder R]

variable [Module K R]

variable (seed : Seed K M R)

variable {seed} (f : Partial seed)

theorem isPartial_sSupFun [IsOrderedAddMonoid R]
    {c : Set (HahnEmbedding.Partial seed)} (hnonempty : c.Nonempty) (hc : DirectedOn (· ≤ ·) c) :
    IsPartial seed (HahnEmbedding.Partial.sSupFun hc) where
  strictMono := HahnEmbedding.Partial.sSupFun_strictMono hnonempty hc
  baseEmbedding_le := HahnEmbedding.Partial.baseEmbedding_le_sSupFun hnonempty hc
  truncLT_mem_range := HahnEmbedding.Partial.truncLT_mem_range_sSupFun hnonempty hc

