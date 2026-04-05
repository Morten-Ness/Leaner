import Mathlib

section

variable {K : Type*} {v : K} {n : ℕ} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

theorem nth_stream_fr_lt_one {ifp_n : GenContFract.IntFractPair K}
    (nth_stream_eq : GenContFract.IntFractPair.stream v n = some ifp_n) : ifp_n.fr < 1 := (GenContFract.IntFractPair.nth_stream_fr_nonneg_lt_one nth_stream_eq).right

end

section

variable {K : Type*} {v : K} {n : ℕ} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

theorem nth_stream_fr_nonneg {ifp_n : GenContFract.IntFractPair K}
    (nth_stream_eq : GenContFract.IntFractPair.stream v n = some ifp_n) : 0 ≤ ifp_n.fr := (GenContFract.IntFractPair.nth_stream_fr_nonneg_lt_one nth_stream_eq).left

end
