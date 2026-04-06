import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [FloorRing K] {v : K}

variable {n : ℕ}

theorem succ_nth_stream_eq_some_iff {ifp_succ_n : GenContFract.IntFractPair K} :
    GenContFract.IntFractPair.stream v (n + 1) = some ifp_succ_n ↔
      ∃ ifp_n : GenContFract.IntFractPair K,
        GenContFract.IntFractPair.stream v n = some ifp_n ∧
          ifp_n.fr ≠ 0 ∧ GenContFract.IntFractPair.of ifp_n.fr⁻¹ = ifp_succ_n := by
  simpa [Nat.add_comm 1 n, Nat.add_left_comm, Nat.add_assoc] using
    (GenContFract.IntFractPair.succ_nth_stream_eq_some_iff (v := v) (n := n)
      (ifp_succ_n := ifp_succ_n))
