import Mathlib

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable {K : Type*} [Ring K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable [Module K M] [PosSMulMono K M]

theorem ball_le_closedBall {c : ArchimedeanClass M} : ball K c ≤ closedBall K c := by
  obtain rfl | hc := eq_or_ne c ⊤
  · simp
  intro a ha
  simpa using ((ArchimedeanClass.mem_ball_iff K hc).mp ha).le

