import Mathlib

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable {K : Type*} [Ring K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable [Module K M] [PosSMulMono K M]

theorem ball_top : ball (M := M) K ⊤ = ⊥ :=
  (Submodule.toAddSubgroup_inj _ _).mp <| ballAddSubgroup_top M

