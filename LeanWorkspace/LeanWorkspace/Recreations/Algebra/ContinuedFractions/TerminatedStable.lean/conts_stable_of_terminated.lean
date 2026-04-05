import Mathlib

variable {K : Type*} {g : GenContFract K} {n m : ℕ}

variable [DivisionRing K]

theorem conts_stable_of_terminated (n_le_m : n ≤ m) (terminatedAt_n : g.TerminatedAt n) :
    g.conts m = g.conts n := by
  simp only [nth_cont_eq_succ_nth_contAux,
    GenContFract.contsAux_stable_of_terminated (Nat.pred_le_iff.mp n_le_m) terminatedAt_n]

