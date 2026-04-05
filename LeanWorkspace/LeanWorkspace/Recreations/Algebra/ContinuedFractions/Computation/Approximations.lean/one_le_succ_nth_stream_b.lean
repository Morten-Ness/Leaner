import Mathlib

variable {K : Type*} {v : K} {n : ℕ} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

theorem one_le_succ_nth_stream_b {ifp_succ_n : GenContFract.IntFractPair K}
    (succ_nth_stream_eq : GenContFract.IntFractPair.stream v (n + 1) = some ifp_succ_n) : 1 ≤ ifp_succ_n.b := by
  obtain ⟨ifp_n, nth_stream_eq, stream_nth_fr_ne_zero, ⟨-⟩⟩ :
      ∃ ifp_n, GenContFract.IntFractPair.stream v n = some ifp_n ∧ ifp_n.fr ≠ 0
        ∧ GenContFract.IntFractPair.of ifp_n.fr⁻¹ = ifp_succ_n :=
    succ_nth_stream_eq_some_iff.1 succ_nth_stream_eq
  rw [GenContFract.IntFractPair.of, le_floor, cast_one, one_le_inv₀
    ((GenContFract.IntFractPair.nth_stream_fr_nonneg nth_stream_eq).lt_of_ne' stream_nth_fr_ne_zero)]
  exact (GenContFract.IntFractPair.nth_stream_fr_lt_one nth_stream_eq).le

