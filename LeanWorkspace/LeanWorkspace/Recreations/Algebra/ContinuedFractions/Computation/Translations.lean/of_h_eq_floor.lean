import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [FloorRing K] {v : K}

theorem of_h_eq_floor : (of v).h = ⌊v⌋ := by
  simp [GenContFract.of_h_eq_intFractPair_seq1_fst_b, IntFractPair.of]

