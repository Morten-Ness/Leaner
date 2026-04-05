import Mathlib

variable {K : Type*} {n : ℕ}

variable {g : GenContFract K} {s : Stream'.Seq <| Pair K}

variable [DivisionRing K]

theorem squashSeq_eq_self_of_terminated (terminatedAt_succ_n : s.TerminatedAt (n + 1)) :
    GenContFract.squashSeq s n = s := by
  change s.get? (n + 1) = none at terminatedAt_succ_n
  cases s_nth_eq : s.get? n <;> simp only [*, GenContFract.squashSeq]

