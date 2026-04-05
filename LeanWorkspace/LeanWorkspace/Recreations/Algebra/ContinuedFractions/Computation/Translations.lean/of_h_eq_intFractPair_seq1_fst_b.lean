import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [FloorRing K] {v : K}

theorem of_h_eq_intFractPair_seq1_fst_b : (of v).h = (IntFractPair.seq1 v).fst.b := by
  cases aux_seq_eq : IntFractPair.seq1 v
  simp [of, aux_seq_eq]

