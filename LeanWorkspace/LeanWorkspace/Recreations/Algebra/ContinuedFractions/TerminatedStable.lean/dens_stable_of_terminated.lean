import Mathlib

variable {K : Type*} {g : GenContFract K} {n m : ℕ}

variable [DivisionRing K]

theorem dens_stable_of_terminated (n_le_m : n ≤ m) (terminatedAt_n : g.TerminatedAt n) :
    g.dens m = g.dens n := by
  simp only [den_eq_conts_b, GenContFract.conts_stable_of_terminated n_le_m terminatedAt_n]

