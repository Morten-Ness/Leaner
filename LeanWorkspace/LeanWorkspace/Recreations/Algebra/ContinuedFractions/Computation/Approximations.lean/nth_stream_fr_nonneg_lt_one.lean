import Mathlib

variable {K : Type*} {v : K} {n : ℕ} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

theorem nth_stream_fr_nonneg_lt_one {ifp_n : GenContFract.IntFractPair K}
    (nth_stream_eq : GenContFract.IntFractPair.stream v n = some ifp_n) : 0 ≤ ifp_n.fr ∧ ifp_n.fr < 1 := by
  cases n with
  | zero =>
    have : GenContFract.IntFractPair.of v = ifp_n := by injection nth_stream_eq
    rw [← this, GenContFract.IntFractPair.of]
    exact ⟨fract_nonneg _, fract_lt_one _⟩
  | succ =>
    rcases succ_nth_stream_eq_some_iff.1 nth_stream_eq with ⟨_, _, _, ifp_of_eq_ifp_n⟩
    rw [← ifp_of_eq_ifp_n, GenContFract.IntFractPair.of]
    exact ⟨fract_nonneg _, fract_lt_one _⟩

