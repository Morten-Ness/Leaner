import Mathlib

section

variable (K : Type*)

variable [DivisionRing K] [LinearOrder K] [FloorRing K]

theorem stream_isSeq (v : K) : (GenContFract.IntFractPair.stream v).IsSeq := by
  intro _ hyp
  simp [GenContFract.IntFractPair.stream, hyp]

end
