import Mathlib

variable {K : Type*} {v : K} {n : ℕ} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

omit [IsStrictOrderedRing K] in
theorem succ_nth_stream_b_le_nth_stream_fr_inv {ifp_n ifp_succ_n : GenContFract.IntFractPair K}
    (nth_stream_eq : GenContFract.IntFractPair.stream v n = some ifp_n)
    (succ_nth_stream_eq : GenContFract.IntFractPair.stream v (n + 1) = some ifp_succ_n) :
    (ifp_succ_n.b : K) ≤ ifp_n.fr⁻¹ := by
  suffices (⌊ifp_n.fr⁻¹⌋ : K) ≤ ifp_n.fr⁻¹ by
    obtain ⟨_, ifp_n_fr⟩ := ifp_n
    have : ifp_n_fr ≠ 0 := by
      intro h
      simp [h, GenContFract.IntFractPair.stream, nth_stream_eq] at succ_nth_stream_eq
    have : GenContFract.IntFractPair.of ifp_n_fr⁻¹ = ifp_succ_n := by
      simpa [this, GenContFract.IntFractPair.stream, nth_stream_eq, Option.coe_def] using succ_nth_stream_eq
    rwa [← this]
  exact floor_le ifp_n.fr⁻¹

