import Mathlib

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable {K : Type*} [Ring K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable [Module K M] [PosSMulMono K M]

theorem toAddSubgroup_ball (c : ArchimedeanClass M) :
    (ball K c).toAddSubgroup = ballAddSubgroup c := rfl

