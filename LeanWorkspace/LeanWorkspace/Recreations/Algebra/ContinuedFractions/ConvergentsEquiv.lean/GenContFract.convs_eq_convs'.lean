import Mathlib

variable {K : Type*} {n : ℕ}

variable {g : GenContFract K} {s : Stream'.Seq <| Pair K}

theorem convs_eq_convs' [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (s_pos : ∀ {gp : Pair K} {m : ℕ}, m < n → g.s.get? m = some gp → 0 < gp.a ∧ 0 < gp.b) :
    g.convs n = g.convs' n := by
  induction n generalizing g with
  | zero => simp
  | succ n IH =>
    let g' := GenContFract.squashGCF g n
    -- first replace the rhs with the squashed computation
    suffices g.convs (n + 1) = g'.convs' n by
      rwa [GenContFract.succ_nth_conv'_eq_squashGCF_nth_conv']
    rcases Decidable.em (TerminatedAt g n) with terminatedAt_n | not_terminatedAt_n
    · have g'_eq_g : g' = g := GenContFract.squashGCF_eq_self_of_terminated terminatedAt_n
      rw [convs_stable_of_terminated n.le_succ terminatedAt_n, g'_eq_g, IH _]
      intro _ _ m_lt_n s_mth_eq
      exact s_pos (Nat.lt_succ_of_lt m_lt_n) s_mth_eq
    · suffices g.convs (n + 1) = g'.convs n by
        -- invoke the IH for the squashed gcf
        rwa [← IH]
        intro gp' m m_lt_n s_mth_eq'
        -- case distinction on m + 1 = n or m + 1 < n
        rcases m_lt_n with n | succ_m_lt_n
        · -- the difficult case at the squashed position: we first obtain the values from
          -- the sequence
          obtain ⟨gp_succ_m, s_succ_mth_eq⟩ : ∃ gp_succ_m, g.s.get? (m + 1) = some gp_succ_m :=
            Option.ne_none_iff_exists'.mp not_terminatedAt_n
          obtain ⟨gp_m, mth_s_eq⟩ : ∃ gp_m, g.s.get? m = some gp_m :=
            g.s.ge_stable m.le_succ s_succ_mth_eq
          -- we then plug them into the recurrence
          suffices 0 < gp_m.a ∧ 0 < gp_m.b + gp_succ_m.a / gp_succ_m.b by
            have ot : g'.s.get? m = some ⟨gp_m.a, gp_m.b + gp_succ_m.a / gp_succ_m.b⟩ :=
              GenContFract.squashSeq_nth_of_not_terminated mth_s_eq s_succ_mth_eq
            grind
          have m_lt_n : m < m.succ := Nat.lt_succ_self m
          refine ⟨(s_pos (Nat.lt_succ_of_lt m_lt_n) mth_s_eq).left, ?_⟩
          refine add_pos (s_pos (Nat.lt_succ_of_lt m_lt_n) mth_s_eq).right ?_
          have : 0 < gp_succ_m.a ∧ 0 < gp_succ_m.b := s_pos (lt_add_one <| m + 1) s_succ_mth_eq
          exact div_pos this.left this.right
        · -- the easy case: before the squashed position, nothing changes
          refine s_pos (Nat.lt_succ_of_lt <| Nat.lt_succ_of_lt succ_m_lt_n) ?_
          exact Eq.trans (GenContFract.squashGCF_nth_of_lt succ_m_lt_n).symm s_mth_eq'
      -- now the result follows from the fact that the convergents coincide at the squashed position
      -- as established in `GenContFract.succ_nth_conv_eq_squashGCF_nth_conv`.
      have : ∀ ⦃b⦄, g.partDens.get? n = some b → b ≠ 0 := by
        intro b nth_partDen_eq
        obtain ⟨gp, s_nth_eq, ⟨refl⟩⟩ : ∃ gp, g.s.get? n = some gp ∧ gp.b = b :=
          exists_s_b_of_partDen nth_partDen_eq
        exact (ne_of_lt (s_pos (lt_add_one n) s_nth_eq).right).symm
      exact GenContFract.succ_nth_conv_eq_squashGCF_nth_conv @this

