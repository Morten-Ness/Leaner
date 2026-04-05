FAIL
import Mathlib

variable {K : Type*} {v : K} {n : ℕ} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

theorem nth_stream_fr_lt_one {ifp_n : GenContFract.IntFractPair K}
    (nth_stream_eq : GenContFract.IntFractPair.stream v n = some ifp_n) : ifp_n.fr < 1 := by
  simpa [GenContFract.IntFractPair.stream] using Option.mem_def.mp ⟨n, nth_stream_eq⟩
