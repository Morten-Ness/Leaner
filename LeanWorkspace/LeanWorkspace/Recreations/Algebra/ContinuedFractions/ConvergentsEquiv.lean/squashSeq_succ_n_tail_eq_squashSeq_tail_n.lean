import Mathlib

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

