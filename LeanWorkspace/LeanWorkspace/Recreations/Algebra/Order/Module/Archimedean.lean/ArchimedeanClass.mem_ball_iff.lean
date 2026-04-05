import Mathlib

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable {K : Type*} [Ring K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable [Module K M] [PosSMulMono K M]

theorem mem_ball_iff {a : M} {c : ArchimedeanClass M} (hc : c ≠ ⊤) : a ∈ ball K c ↔ c < ArchimedeanClass.mk a := mem_ballAddSubgroup_iff hc

