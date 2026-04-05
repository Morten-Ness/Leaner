import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [FloorRing K] {v : K}

variable {n : ℕ}

theorem of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none :
    (of v).TerminatedAt n ↔ IntFractPair.stream v (n + 1) = none := by
  rw [GenContFract.of_terminatedAt_iff_intFractPair_seq1_terminatedAt, Stream'.Seq.TerminatedAt,
    GenContFract.IntFractPair.get?_seq1_eq_succ_get?_stream]

