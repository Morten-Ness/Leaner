import Mathlib

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

