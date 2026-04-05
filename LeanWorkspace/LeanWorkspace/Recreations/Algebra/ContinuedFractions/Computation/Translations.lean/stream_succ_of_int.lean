import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [FloorRing K] {v : K}

variable {n : ℕ}

theorem stream_succ_of_int [IsStrictOrderedRing K] (a : ℤ) (n : ℕ) :
    GenContFract.IntFractPair.stream (a : K) (n + 1) = none := by
  induction n with
  | zero =>
    refine GenContFract.IntFractPair.stream_eq_none_of_fr_eq_zero (GenContFract.IntFractPair.stream_zero (a : K)) ?_
    simp only [GenContFract.IntFractPair.of, Int.fract_intCast]
  | succ n ih => exact GenContFract.IntFractPair.succ_nth_stream_eq_none_iff.mpr (Or.inl ih)

