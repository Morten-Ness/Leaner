import Mathlib

variable {K : Type*} {g : GenContFract K} {n m : ℕ}

variable [DivisionRing K]

theorem nums_stable_of_terminated (n_le_m : n ≤ m) (terminatedAt_n : g.TerminatedAt n) :
    g.nums m = g.nums n := by
  simp only [num_eq_conts_a, GenContFract.conts_stable_of_terminated n_le_m terminatedAt_n]

