import Mathlib

variable {K : Type*} {g : GenContFract K} {n m : ℕ}

variable [DivisionRing K]

theorem contsAux_stable_of_terminated (n_lt_m : n < m) (terminatedAt_n : g.TerminatedAt n) :
    g.contsAux m = g.contsAux (n + 1) := by
  simpa using g.contsAux_stable_of_terminated n_lt_m terminatedAt_n
