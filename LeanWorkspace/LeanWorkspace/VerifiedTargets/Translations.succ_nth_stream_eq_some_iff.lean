import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [FloorRing K] {v : K}

variable {n : ℕ}

theorem succ_nth_stream_eq_some_iff {ifp_succ_n : GenContFract.IntFractPair K} :
    GenContFract.IntFractPair.stream v (n + 1) = some ifp_succ_n ↔
      ∃ ifp_n : GenContFract.IntFractPair K,
        GenContFract.IntFractPair.stream v n = some ifp_n ∧
          ifp_n.fr ≠ 0 ∧ GenContFract.IntFractPair.of ifp_n.fr⁻¹ = ifp_succ_n := by
  simp [GenContFract.IntFractPair.stream, ite_eq_iff, Option.bind_eq_some_iff]

