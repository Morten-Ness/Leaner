import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable [Module K M] [IsOrderedModule K M]

variable {R : Type*} [AddCommGroup R] [LinearOrder R]

variable [Module K R]

variable (seed : Seed K M R)

variable {seed} (f : Partial seed)

set_option backward.isDefEq.respectTransparency false in
theorem mem_domain {x : M} {c : FiniteArchimedeanClass M} (hx : x ∈ seed.stratum c) :
    x ∈ f.val.domain := by
  apply Set.mem_of_subset_of_mem f.prop.baseEmbedding_le.1
  apply HahnEmbedding.Seed.mem_domain_baseEmbedding seed hx

