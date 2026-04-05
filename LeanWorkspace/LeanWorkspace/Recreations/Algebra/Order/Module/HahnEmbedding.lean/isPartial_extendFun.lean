import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable [Module K M] [IsOrderedModule K M]

variable {R : Type*} [AddCommGroup R] [LinearOrder R]

variable [Module K R]

variable (seed : Seed K M R)

variable {seed} (f : Partial seed)

set_option backward.isDefEq.respectTransparency false in
theorem isPartial_extendFun [IsOrderedAddMonoid R] [Archimedean R] {x : M}
    (hx : x ∉ f.val.domain) : IsPartial seed (HahnEmbedding.Partial.extendFun f hx) where
  strictMono := HahnEmbedding.Partial.extendFun_strictMono f hx
  baseEmbedding_le := HahnEmbedding.Partial.baseEmbedding_le_extendFun f hx
  truncLT_mem_range := HahnEmbedding.Partial.truncLT_mem_range_extendFun f hx

