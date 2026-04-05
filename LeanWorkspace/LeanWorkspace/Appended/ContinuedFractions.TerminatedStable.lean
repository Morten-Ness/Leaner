import Mathlib

section

variable {K : Type*} {g : GenContFract K} {n m : ℕ}

variable [DivisionRing K]

theorem contsAux_stable_of_terminated (n_lt_m : n < m) (terminatedAt_n : g.TerminatedAt n) :
    g.contsAux m = g.contsAux (n + 1) := by
  refine Nat.le_induction rfl (fun k hnk hk => ?_) _ n_lt_m
  rcases Nat.exists_eq_add_of_lt hnk with ⟨k, rfl⟩
  refine (GenContFract.contsAux_stable_step_of_terminated ?_).trans hk
  exact GenContFract.terminated_stable (Nat.le_add_right _ _) terminatedAt_n

end

section

variable {K : Type*} {g : GenContFract K} {n m : ℕ}

theorem terminated_stable (n_le_m : n ≤ m) (terminatedAt_n : g.TerminatedAt n) :
    g.TerminatedAt m := g.s.terminated_stable n_le_m terminatedAt_n

end
