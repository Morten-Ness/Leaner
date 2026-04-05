import Mathlib

variable {K : Type*} {g : GenContFract K} {n m : ℕ}

variable [DivisionRing K]

theorem convs'_stable_of_terminated (n_le_m : n ≤ m) (terminatedAt_n : g.TerminatedAt n) :
    g.convs' m = g.convs' n := by
  simp only [convs', GenContFract.convs'Aux_stable_of_terminated n_le_m terminatedAt_n]

