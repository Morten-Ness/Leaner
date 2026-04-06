FAIL
import Mathlib

variable (K : Type*)

variable [DivisionRing K] [LinearOrder K] [FloorRing K]

theorem stream_isSeq (v : K) : (GenContFract.IntFractPair.stream v).IsSeq := by
  intro n h
  simpa [GenContFract.IntFractPair.stream] using h
