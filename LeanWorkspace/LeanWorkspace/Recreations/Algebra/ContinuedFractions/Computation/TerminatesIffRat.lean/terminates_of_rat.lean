import Mathlib

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

theorem terminates_of_rat (q : ℚ) : (of q).Terminates := Exists.elim (IntFractPair.exists_nth_stream_eq_none_of_rat q) fun n stream_nth_eq_none =>
    Exists.intro n
      (have : IntFractPair.stream q (n + 1) = none := IntFractPair.stream_isSeq q stream_nth_eq_none
      of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none.mpr this)

