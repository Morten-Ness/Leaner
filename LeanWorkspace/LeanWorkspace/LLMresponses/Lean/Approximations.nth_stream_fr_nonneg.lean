FAIL
import Mathlib

variable {K : Type*} {v : K} {n : ℕ} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

theorem nth_stream_fr_nonneg {ifp_n : GenContFract.IntFractPair K}
    (nth_stream_eq : GenContFract.IntFractPair.stream v n = some ifp_n) : 0 ≤ ifp_n.fr := by
  induction n generalizing v with
  | zero =>
      simp [GenContFract.IntFractPair.stream] at nth_stream_eq
      rw [← nth_stream_eq]
      exact Int.fract_nonneg v
  | succ n ih =>
      simp [GenContFract.IntFractPair.stream] at nth_stream_eq
      cases h : GenContFract.IntFractPair.stream v n with
      | none =>
          simp [h] at nth_stream_eq
      | some ap_n =>
          simp [h] at nth_stream_eq
          split_ifs at nth_stream_eq with hfr
          · simp at nth_stream_eq
          · exact ih nth_stream_eq
