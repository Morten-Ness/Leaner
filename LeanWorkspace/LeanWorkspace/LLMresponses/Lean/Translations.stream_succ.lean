import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [FloorRing K] {v : K}

variable {n : ℕ}

theorem stream_succ (h : Int.fract v ≠ 0) (n : ℕ) :
    GenContFract.IntFractPair.stream v (n + 1) = GenContFract.IntFractPair.stream (Int.fract v)⁻¹ n := by
  simpa [Nat.add_comm] using GenContFract.IntFractPair.stream_succ (v := v) h n
