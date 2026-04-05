import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [FloorRing K] {v : K}

variable {n : ℕ}

theorem exists_succ_nth_stream_of_fr_zero {ifp_succ_n : GenContFract.IntFractPair K}
    (stream_succ_nth_eq : GenContFract.IntFractPair.stream v (n + 1) = some ifp_succ_n)
    (succ_nth_fr_eq_zero : ifp_succ_n.fr = 0) :
    ∃ ifp_n : GenContFract.IntFractPair K, GenContFract.IntFractPair.stream v n = some ifp_n ∧ ifp_n.fr⁻¹ = ⌊ifp_n.fr⁻¹⌋ := by
  -- get the witness from `GenContFract.IntFractPair.succ_nth_stream_eq_some_iff` and prove that it has the additional
  -- properties
  rcases GenContFract.IntFractPair.succ_nth_stream_eq_some_iff.mp stream_succ_nth_eq with
    ⟨ifp_n, seq_nth_eq, _, rfl⟩
  refine ⟨ifp_n, seq_nth_eq, ?_⟩
  simpa only [GenContFract.IntFractPair.of, Int.fract, sub_eq_zero] using succ_nth_fr_eq_zero

