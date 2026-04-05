import Mathlib

variable {K : Type*} {g : GenContFract K} {n m : ℕ}

variable [DivisionRing K]

theorem convs'Aux_stable_of_terminated {s : Stream'.Seq <| Pair K} (n_le_m : n ≤ m)
    (terminatedAt_n : s.TerminatedAt n) : convs'Aux s m = convs'Aux s n := by
  induction n_le_m with
  | refl => rfl
  | step n_le_m IH =>
    refine (GenContFract.convs'Aux_stable_step_of_terminated (?_)).trans IH
    exact GenContFract.terminated_stable s n_le_m terminatedAt_n

