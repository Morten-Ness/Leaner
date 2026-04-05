import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable [Module K M] [IsOrderedModule K M]

variable {R : Type*} [AddCommGroup R] [LinearOrder R]

variable [Module K R]

variable (u : ArchimedeanStrata K M) {c : FiniteArchimedeanClass M}

theorem stratum_ne_bot : u.stratum c ≠ ⊥ := fun eq ↦ (eq ▸ u.ball_sup_stratum_eq c).not_lt <| by simpa using ball_lt_closedBall _

