FAIL
import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [FloorRing K] {v : K}

variable {n : ℕ}

theorem stream_succ_of_int [IsStrictOrderedRing K] (a : ℤ) (n : ℕ) :
    GenContFract.IntFractPair.stream (a : K) (n + 1) = none := by
  induction n with
  | zero =>
      simp [GenContFract.IntFractPair.stream, GenContFract.IntFractPair.of]
  | succ n ih =>
      simp [GenContFract.IntFractPair.stream, ih]
