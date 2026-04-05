import Mathlib

variable {K : Type*} {v : K} {n : ℕ} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

theorem fib_le_of_contsAux_b :
    n ≤ 1 ∨ ¬(of v).TerminatedAt (n - 2) → (fib n : K) ≤ ((of v).contsAux n).b := Nat.strong_induction_on n
    (by
      intro n IH hyp
      rcases n with (_ | _ | n)
      · simp [contsAux] -- case n = 0
      · simp -- case n = 1
      · let g := of v -- case 2 ≤ n
        have : ¬n + 2 ≤ 1 := by lia
        have not_terminatedAt_n : ¬g.TerminatedAt n := Or.resolve_left hyp this
        obtain ⟨gp, s_ppred_nth_eq⟩ : ∃ gp, g.s.get? n = some gp :=
          Option.ne_none_iff_exists'.mp not_terminatedAt_n
        set pconts := g.contsAux (n + 1) with pconts_eq
        set ppconts := g.contsAux n with ppconts_eq
        -- use the recurrence of `contsAux`
        simp only [Nat.add_assoc, Nat.reduceAdd]
        suffices (fib n : K) + fib (n + 1) ≤ gp.a * ppconts.b + gp.b * pconts.b by
          simpa [g, fib_add_two, add_comm, contsAux_recurrence s_ppred_nth_eq ppconts_eq pconts_eq]
        -- make use of the fact that `gp.a = 1`
        suffices (fib n : K) + fib (n + 1) ≤ ppconts.b + gp.b * pconts.b by
          simpa [GenContFract.of_partNum_eq_one <| partNum_eq_s_a s_ppred_nth_eq]
        have not_terminatedAt_pred_n : ¬g.TerminatedAt (n - 1) :=
          mt (terminated_stable <| Nat.sub_le n 1) not_terminatedAt_n
        have not_terminatedAt_ppred_n : ¬TerminatedAt g (n - 2) :=
          mt (terminated_stable (n - 1).pred_le) not_terminatedAt_pred_n
        -- use the IH to get the inequalities for `pconts` and `ppconts`
        have ppred_nth_fib_le_ppconts_B : (fib n : K) ≤ ppconts.b :=
          IH n (lt_trans (Nat.lt_add_one n) <| Nat.lt_add_one <| n + 1)
            (Or.inr not_terminatedAt_ppred_n)
        suffices (fib (n + 1) : K) ≤ gp.b * pconts.b by gcongr
        -- finally use the fact that `1 ≤ gp.b` to solve the goal
        suffices 1 * (fib (n + 1) : K) ≤ gp.b * pconts.b by rwa [one_mul] at this
        have one_le_gp_b : (1 : K) ≤ gp.b :=
          GenContFract.of_one_le_get?_partDen (partDen_eq_s_b s_ppred_nth_eq)
        gcongr
        grind)

