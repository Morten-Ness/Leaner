import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable [Module K M] [IsOrderedModule K M]

variable {R : Type*} [AddCommGroup R] [LinearOrder R]

variable [Module K R]

variable (seed : Seed K M R)

set_option backward.isDefEq.respectTransparency false in
theorem coeff_baseEmbedding {x : seed.baseEmbedding.domain} {f : Π₀ c, seed.stratum c}
    (h : x.val = f.sum fun c ↦ (seed.stratum c).subtype) (c : FiniteArchimedeanClass M) :
    (ofLex ((HahnEmbedding.Seed.baseEmbedding seed) x)).coeff c = seed.coeff c (f c) := by
  simpa [HahnEmbedding.Seed.baseEmbedding] using HahnEmbedding.Seed.hahnCoeff_apply seed h c

