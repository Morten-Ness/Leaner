import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable [Module K M] [IsOrderedModule K M]

variable {R : Type*} [AddCommGroup R] [LinearOrder R]

variable [Module K R]

variable (u : ArchimedeanStrata K M) {c : FiniteArchimedeanClass M}

theorem archimedeanClassMk_of_mem_stratum {a : M}
    (ha : a ∈ u.stratum c) (h0 : a ≠ 0) : ArchimedeanClass.mk a = c := by
  apply le_antisymm
  · contrapose! h0 with hlt
    have ha' : a ∈ ball K c := (mem_ball_iff K).mpr fun _ ↦ hlt
    exact (Submodule.disjoint_def.mp (u.disjoint_ball_stratum _)) _ ha' ha
  · apply (mem_closedBall_iff K).mp _ h0
    rw [← u.ball_sup_stratum_eq c]
    exact Submodule.mem_sup_right ha

