import Mathlib

section

variable {K : Type*} {n : ℕ}

variable {g : GenContFract K} {s : Stream'.Seq <| Pair K}

variable [DivisionRing K]

theorem contsAux_eq_contsAux_squashGCF_of_le {m : ℕ} :
    m ≤ n → contsAux g m = (GenContFract.squashGCF g n).contsAux m := Nat.strong_induction_on m
    (by
      clear m
      intro m IH m_le_n
      rcases m with - | m'
      · rfl
      · rcases n with - | n'
        · exact (m'.not_succ_le_zero m_le_n).elim
        -- 1 ≰ 0
        · rcases m' with - | m''
          · rfl
          · -- get some inequalities to instantiate the IH for m'' and m'' + 1
            have m'_lt_n : m'' + 1 < n' + 1 := m_le_n
            have succ_m''th_contsAux_eq := IH (m'' + 1) (lt_add_one (m'' + 1)) m'_lt_n.le
            have : m'' < m'' + 2 := lt_add_of_pos_right m'' zero_lt_two
            have m''th_contsAux_eq := IH m'' this (le_trans this.le m_le_n)
            have : (GenContFract.squashGCF g (n' + 1)).s.get? m'' = g.s.get? m'' :=
              GenContFract.squashGCF_nth_of_lt (Nat.succ_lt_succ_iff.mp m'_lt_n)
            simp [contsAux, succ_m''th_contsAux_eq, m''th_contsAux_eq, this])

end

section

variable {K : Type*} {n : ℕ}

variable {g : GenContFract K} {s : Stream'.Seq <| Pair K}

variable [DivisionRing K]

theorem squashGCF_eq_self_of_terminated (terminatedAt_n : TerminatedAt g n) :
    GenContFract.squashGCF g n = g := by
  cases n with
  | zero =>
    change g.s.get? 0 = none at terminatedAt_n
    simp only [GenContFract.squashGCF, terminatedAt_n]
  | succ =>
    cases g
    simp only [GenContFract.squashGCF, GenContFract.mk.injEq, true_and]
    exact GenContFract.squashSeq_eq_self_of_terminated terminatedAt_n

end

section

variable {K : Type*} {n : ℕ}

variable {g : GenContFract K} {s : Stream'.Seq <| Pair K}

variable [DivisionRing K]

theorem squashGCF_nth_of_lt {m : ℕ} (m_lt_n : m < n) :
    (GenContFract.squashGCF g (n + 1)).s.get? m = g.s.get? m := by
  simp only [GenContFract.squashGCF, GenContFract.squashSeq_nth_of_lt m_lt_n]

end

section

variable {K : Type*} {n : ℕ}

variable {g : GenContFract K} {s : Stream'.Seq <| Pair K}

variable [DivisionRing K]

theorem squashSeq_eq_self_of_terminated (terminatedAt_succ_n : s.TerminatedAt (n + 1)) :
    GenContFract.squashSeq s n = s := by
  change s.get? (n + 1) = none at terminatedAt_succ_n
  cases s_nth_eq : s.get? n <;> simp only [*, GenContFract.squashSeq]

end

section

variable {K : Type*} {n : ℕ}

variable {g : GenContFract K} {s : Stream'.Seq <| Pair K}

variable [DivisionRing K]

theorem squashSeq_nth_of_lt {m : ℕ} (m_lt_n : m < n) : (GenContFract.squashSeq s n).get? m = s.get? m := by
  cases s_succ_nth_eq : s.get? (n + 1) with
  | none => rw [GenContFract.squashSeq_eq_self_of_terminated s_succ_nth_eq]
  | some =>
    obtain ⟨gp_n, s_nth_eq⟩ : ∃ gp_n, s.get? n = some gp_n :=
      s.ge_stable n.le_succ s_succ_nth_eq
    simp [*, GenContFract.squashSeq, m_lt_n.ne]

end

section

variable {K : Type*} {n : ℕ}

variable {g : GenContFract K} {s : Stream'.Seq <| Pair K}

variable [DivisionRing K]

theorem squashSeq_nth_of_not_terminated {gp_n gp_succ_n : Pair K} (s_nth_eq : s.get? n = some gp_n)
    (s_succ_nth_eq : s.get? (n + 1) = some gp_succ_n) :
    (GenContFract.squashSeq s n).get? n = some ⟨gp_n.a, gp_n.b + gp_succ_n.a / gp_succ_n.b⟩ := by
  simp [*, GenContFract.squashSeq]

end

section

variable {K : Type*} {n : ℕ}

variable {g : GenContFract K} {s : Stream'.Seq <| Pair K}

variable [DivisionRing K]

theorem squashSeq_succ_n_tail_eq_squashSeq_tail_n :
    (GenContFract.squashSeq s (n + 1)).tail = GenContFract.squashSeq s.tail n := by
  cases s_succ_succ_nth_eq : s.get? (n + 2) with
  | none =>
    cases s_succ_nth_eq : s.get? (n + 1) <;>
      simp only [GenContFract.squashSeq, Stream'.Seq.get?_tail, s_succ_nth_eq, s_succ_succ_nth_eq]
  | some gp_succ_succ_n =>
    obtain ⟨gp_succ_n, s_succ_nth_eq⟩ : ∃ gp_succ_n, s.get? (n + 1) = some gp_succ_n :=
      s.ge_stable (n + 1).le_succ s_succ_succ_nth_eq
    -- apply extensionality with `m` and continue by cases `m = n`.
    ext1 m
    rcases Decidable.em (m = n) with m_eq_n | m_ne_n
    · simp [*, GenContFract.squashSeq]
    · cases s_succ_mth_eq : s.get? (m + 1)
      · simp only [*, GenContFract.squashSeq, Stream'.Seq.get?_tail, Stream'.Seq.get?_zipWith,
          Option.map₂_none_right]
      · simp [*, GenContFract.squashSeq]

end

section

variable {K : Type*} {n : ℕ}

variable {g : GenContFract K} {s : Stream'.Seq <| Pair K}

variable [DivisionRing K]

theorem succ_nth_conv'_eq_squashGCF_nth_conv' :
    g.convs' (n + 1) = (GenContFract.squashGCF g n).convs' n := by
  cases n with
  | zero =>
    cases g_s_head_eq : g.s.get? 0 <;>
      simp [g_s_head_eq, GenContFract.squashGCF, convs', convs'Aux, Stream'.Seq.head]
  | succ =>
    simp only [GenContFract.succ_succ_nth_conv'Aux_eq_succ_nth_conv'Aux_squashSeq, convs',
      GenContFract.squashGCF]

end

section

variable {K : Type*} {n : ℕ}

variable {g : GenContFract K} {s : Stream'.Seq <| Pair K}

theorem succ_nth_conv_eq_squashGCF_nth_conv [Field K]
    (nth_partDen_ne_zero : ∀ {b : K}, g.partDens.get? n = some b → b ≠ 0) :
    g.convs (n + 1) = (GenContFract.squashGCF g n).convs n := by
  rcases Decidable.em (g.TerminatedAt n) with terminatedAt_n | not_terminatedAt_n
  · have : GenContFract.squashGCF g n = g := GenContFract.squashGCF_eq_self_of_terminated terminatedAt_n
    simp only [this, convs_stable_of_terminated n.le_succ terminatedAt_n]
  · obtain ⟨⟨a, b⟩, s_nth_eq⟩ : ∃ gp_n, g.s.get? n = some gp_n :=
      Option.ne_none_iff_exists'.mp not_terminatedAt_n
    have b_ne_zero : b ≠ 0 := nth_partDen_ne_zero (partDen_eq_s_b s_nth_eq)
    cases n with
    | zero =>
      suffices (b * g.h + a) / b = g.h + a / b by
        simpa [GenContFract.squashGCF, s_nth_eq, conv_eq_conts_a_div_conts_b,
          conts_recurrenceAux s_nth_eq zeroth_contAux_eq_one_zero first_contAux_eq_h_one]
      grind
    | succ n' =>
      obtain ⟨⟨pa, pb⟩, s_n'th_eq⟩ : ∃ gp_n', g.s.get? n' = some gp_n' :=
        g.s.ge_stable n'.le_succ s_nth_eq
      -- Notations
      let g' := GenContFract.squashGCF g (n' + 1)
      set pred_conts := g.contsAux (n' + 1) with succ_n'th_contsAux_eq
      set ppred_conts := g.contsAux n' with n'th_contsAux_eq
      let pA := pred_conts.a
      let pB := pred_conts.b
      let ppA := ppred_conts.a
      let ppB := ppred_conts.b
      set pred_conts' := g'.contsAux (n' + 1) with succ_n'th_contsAux_eq'
      set ppred_conts' := g'.contsAux n' with n'th_contsAux_eq'
      let pA' := pred_conts'.a
      let pB' := pred_conts'.b
      let ppA' := ppred_conts'.a
      let ppB' := ppred_conts'.b
      -- first compute the convergent of the squashed gcf
      have : g'.convs (n' + 1) =
          ((pb + a / b) * pA' + pa * ppA') / ((pb + a / b) * pB' + pa * ppB') := by
        have : g'.s.get? n' = some ⟨pa, pb + a / b⟩ :=
          GenContFract.squashSeq_nth_of_not_terminated s_n'th_eq s_nth_eq
        rw [conv_eq_conts_a_div_conts_b,
          conts_recurrenceAux this n'th_contsAux_eq'.symm succ_n'th_contsAux_eq'.symm]
      rw [this]
      -- then compute the convergent of the original gcf by recursively unfolding the continuants
      -- computation twice
      have : g.convs (n' + 2) =
          (b * (pb * pA + pa * ppA) + a * pA) / (b * (pb * pB + pa * ppB) + a * pB) := by
        -- use the recurrence once
        have : g.contsAux (n' + 2) = ⟨pb * pA + pa * ppA, pb * pB + pa * ppB⟩ :=
          contsAux_recurrence s_n'th_eq n'th_contsAux_eq.symm succ_n'th_contsAux_eq.symm
        -- and a second time
        rw [conv_eq_conts_a_div_conts_b,
          conts_recurrenceAux s_nth_eq succ_n'th_contsAux_eq.symm this]
      rw [this]
      suffices
        ((pb + a / b) * pA + pa * ppA) / ((pb + a / b) * pB + pa * ppB) =
          (b * (pb * pA + pa * ppA) + a * pA) / (b * (pb * pB + pa * ppB) + a * pB) by
        obtain ⟨eq1, eq2, eq3, eq4⟩ : pA' = pA ∧ pB' = pB ∧ ppA' = ppA ∧ ppB' = ppB := by
          simp [*, g', pA, pB, ppA, ppB, pA', pB', ppA', ppB',
            (GenContFract.contsAux_eq_contsAux_squashGCF_of_le <| le_refl <| n' + 1).symm,
            (GenContFract.contsAux_eq_contsAux_squashGCF_of_le n'.le_succ).symm]
        symm
        simpa only [eq1, eq2, eq3, eq4, mul_div_cancel_right₀ _ b_ne_zero]
      grind

end

section

variable {K : Type*} {n : ℕ}

variable {g : GenContFract K} {s : Stream'.Seq <| Pair K}

variable [DivisionRing K]

theorem succ_succ_nth_conv'Aux_eq_succ_nth_conv'Aux_squashSeq :
    convs'Aux s (n + 2) = convs'Aux (GenContFract.squashSeq s n) (n + 1) := by
  cases s_succ_nth_eq : s.get? <| n + 1 with
  | none =>
    rw [GenContFract.squashSeq_eq_self_of_terminated s_succ_nth_eq,
      convs'Aux_stable_step_of_terminated s_succ_nth_eq]
  | some gp_succ_n =>
    induction n generalizing s gp_succ_n with
    | zero =>
      obtain ⟨gp_head, s_head_eq⟩ : ∃ gp_head, s.head = some gp_head :=
        s.ge_stable zero_le_one s_succ_nth_eq
      have : (GenContFract.squashSeq s 0).head = some ⟨gp_head.a, gp_head.b + gp_succ_n.a / gp_succ_n.b⟩ :=
        GenContFract.squashSeq_nth_of_not_terminated s_head_eq s_succ_nth_eq
      simp_all [convs'Aux, Stream'.Seq.head, Stream'.Seq.get?_tail]
    | succ m IH =>
      obtain ⟨gp_head, s_head_eq⟩ : ∃ gp_head, s.head = some gp_head :=
        s.ge_stable (m + 2).zero_le s_succ_nth_eq
      suffices
        gp_head.a / (gp_head.b + convs'Aux s.tail (m + 2)) =
          convs'Aux (GenContFract.squashSeq s (m + 1)) (m + 2)
        by simpa only [convs'Aux, s_head_eq]
      have : (GenContFract.squashSeq s (m + 1)).head = some gp_head :=
        (GenContFract.squashSeq_nth_of_lt m.succ_pos).trans s_head_eq
      simp_all [convs'Aux, GenContFract.squashSeq_succ_n_tail_eq_squashSeq_tail_n]

end
