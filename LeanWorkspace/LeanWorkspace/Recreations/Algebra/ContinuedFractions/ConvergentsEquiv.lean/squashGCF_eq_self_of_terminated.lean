import Mathlib

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

