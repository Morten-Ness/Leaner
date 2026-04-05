import Mathlib

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

