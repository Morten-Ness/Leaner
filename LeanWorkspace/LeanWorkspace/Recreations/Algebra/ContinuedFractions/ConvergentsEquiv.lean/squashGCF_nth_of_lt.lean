import Mathlib

variable {K : Type*} {n : ℕ}

variable {g : GenContFract K} {s : Stream'.Seq <| Pair K}

variable [DivisionRing K]

theorem squashGCF_nth_of_lt {m : ℕ} (m_lt_n : m < n) :
    (GenContFract.squashGCF g (n + 1)).s.get? m = g.s.get? m := by
  simp only [GenContFract.squashGCF, GenContFract.squashSeq_nth_of_lt m_lt_n]

