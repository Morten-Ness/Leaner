FAIL
import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [FloorRing K] {v : K}

variable {n : ℕ}

theorem exists_succ_nth_stream_of_fr_zero {ifp_succ_n : GenContFract.IntFractPair K}
    (stream_succ_nth_eq : GenContFract.IntFractPair.stream v (n + 1) = some ifp_succ_n)
    (succ_nth_fr_eq_zero : ifp_succ_n.fr = 0) :
    ∃ ifp_n : GenContFract.IntFractPair K, GenContFract.IntFractPair.stream v n = some ifp_n ∧ ifp_n.fr⁻¹ = ⌊ifp_n.fr⁻¹⌋ := by
  classical
  cases h : GenContFract.IntFractPair.stream v n with
  | none =>
      simp [GenContFract.IntFractPair.stream, h] at stream_succ_nth_eq
  | some ifp_n =>
      refine ⟨ifp_n, h, ?_⟩
      simp [GenContFract.IntFractPair.stream, h] at stream_succ_nth_eq
      rcases stream_succ_nth_eq with ⟨hnez, hof⟩
      have hfrinv_zero : ifp_n.fr⁻¹ = 0 := by
        have : (GenContFract.IntFractPair.of (ifp_n.fr⁻¹)).fr = 0 := by
          rw [hof, succ_nth_fr_eq_zero]
        simpa [GenContFract.IntFractPair.of] using this
      rw [hfrinv_zero, Int.floor_zero]
