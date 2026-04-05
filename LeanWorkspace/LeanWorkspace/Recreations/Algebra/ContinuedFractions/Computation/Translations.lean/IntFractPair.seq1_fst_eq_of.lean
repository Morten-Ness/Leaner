import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [FloorRing K] {v : K}

theorem IntFractPair.seq1_fst_eq_of : (IntFractPair.seq1 v).fst = IntFractPair.of v := rfl

