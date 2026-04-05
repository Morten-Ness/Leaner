import Mathlib

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable {K : Type*} [Ring K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable [Module K M] [PosSMulMono K M]

theorem mem_closedBall_iff {a : M} {c : ArchimedeanClass M} : a ∈ closedBall K c ↔ c ≤ ArchimedeanClass.mk a := mem_closedBallAddSubgroup_iff

