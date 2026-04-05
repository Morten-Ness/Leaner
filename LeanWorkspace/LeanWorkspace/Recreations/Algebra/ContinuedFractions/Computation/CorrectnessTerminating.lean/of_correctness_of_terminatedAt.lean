import Mathlib

variable {K : Type*} [Field K] [LinearOrder K] {v : K} {n : ℕ}

variable [FloorRing K]

theorem of_correctness_of_terminatedAt (terminatedAt_n : (of v).TerminatedAt n) :
    v = (of v).convs n := have : IntFractPair.stream v (n + 1) = none :=
    of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none.1 terminatedAt_n
  GenContFract.of_correctness_of_nth_stream_eq_none this

