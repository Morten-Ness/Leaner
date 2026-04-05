import Mathlib

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable {K : Type*} [Ring K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable [Module K M] [PosSMulMono K M]

theorem toAddSubgroup_closedBall (c : ArchimedeanClass M) :
    (closedBall K c).toAddSubgroup = closedBallAddSubgroup c := rfl

