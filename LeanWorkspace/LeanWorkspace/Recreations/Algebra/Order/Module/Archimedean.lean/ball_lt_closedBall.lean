import Mathlib

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable {K : Type*} [Ring K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable [Module K M] [PosSMulMono K M]

theorem ball_lt_closedBall {c : FiniteArchimedeanClass M} : ball K c < closedBall K c := FiniteArchimedeanClass.submodule_strictAnti _ Set.Ioi_ssubset_Ici_self

attribute [deprecated FiniteArchimedeanClass.submodule (since := "2025-12-14")] ArchimedeanClass.submodule
attribute [deprecated ball (since := "2025-12-14")] ArchimedeanClass.ball
attribute [deprecated closedBall (since := "2025-12-14")] ArchimedeanClass.closedBall
attribute [deprecated FiniteArchimedeanClass.toAddSubgroup_ball (since := "2025-12-14")]
  ArchimedeanClass.toAddSubgroup_ball
attribute [deprecated FiniteArchimedeanClass.toAddSubgroup_closedBall (since := "2025-12-14")]
  ArchimedeanClass.toAddSubgroup_closedBall
attribute [deprecated FiniteArchimedeanClass.mem_ball_iff (since := "2025-12-14")] ArchimedeanClass.mem_ball_iff
attribute [deprecated FiniteArchimedeanClass.mem_closedBall_iff (since := "2025-12-14")]
  ArchimedeanClass.mem_closedBall_iff
attribute [deprecated "Lemma for junk value." (since := "2025-12-14")] ArchimedeanClass.ball_top
attribute [deprecated "Lemma for junk value." (since := "2025-12-14")]
  ArchimedeanClass.closedBall_top
attribute [deprecated FiniteArchimedeanClass.ball_strictAnti (since := "2025-12-14")] ArchimedeanClass.ball_antitone
attribute [deprecated ball_lt_closedBall (since := "2025-12-14")]
  ArchimedeanClass.ball_le_closedBall

