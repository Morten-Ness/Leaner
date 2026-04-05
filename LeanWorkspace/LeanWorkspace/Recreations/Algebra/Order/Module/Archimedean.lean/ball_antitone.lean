import Mathlib

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable {K : Type*} [Ring K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable [Module K M] [PosSMulMono K M]

theorem ball_antitone : Antitone (ball (M := M) K) := by
  intro _ _ h
  exact (Submodule.toAddSubgroup_le _ _).mp <| ballAddSubgroup_antitone h

