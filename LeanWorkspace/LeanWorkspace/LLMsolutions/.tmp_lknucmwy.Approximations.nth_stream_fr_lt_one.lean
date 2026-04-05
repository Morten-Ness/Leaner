import Mathlib

variable {K : Type*} {v : K} {n : ℕ} [LinearOrderedField K] [FloorRing K]

theorem nth_stream_fr_lt_one {ifp_n : GenContFract.IntFractPair K}
    (nth_stream_eq : GenContFract.IntFractPair.stream v n = some ifp_n) : ifp_n.fr < 1 := by
  simpa using GenContFract.IntFractPair.stream_nth_fr_lt_one nth_stream_eq
