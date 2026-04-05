FAIL
import Mathlib

variable {K : Type*} {v : K} {n : ℕ} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

theorem nth_stream_fr_nonneg {ifp_n : GenContFract.IntFractPair K}
    (nth_stream_eq : GenContFract.IntFractPair.stream v n = some ifp_n) : 0 ≤ ifp_n.fr := by
  simpa [GenContFract.IntFractPair.stream_eq_some_iff] using nth_stream_eq
