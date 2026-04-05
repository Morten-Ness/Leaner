import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [FloorRing K] {v : K}

theorem stream_zero (v : K) : GenContFract.IntFractPair.stream v 0 = some (GenContFract.IntFractPair.of v) := rfl

