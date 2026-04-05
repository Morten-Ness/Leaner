import Mathlib

variable {K : Type*} {g : GenContFract K} {n m : ℕ}

variable [DivisionRing K]

theorem contsAux_stable_step_of_terminated (terminatedAt_n : g.TerminatedAt n) :
    g.contsAux (n + 2) = g.contsAux (n + 1) := by
  rw [terminatedAt_iff_s_none] at terminatedAt_n
  simp only [contsAux, terminatedAt_n]

