import Mathlib

variable {K : Type*} {g : GenContFract K} {n m : ℕ}

theorem terminated_stable (n_le_m : n ≤ m) (terminatedAt_n : g.TerminatedAt n) :
    g.TerminatedAt m := g.s.terminated_stable n_le_m terminatedAt_n

