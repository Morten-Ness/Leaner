import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [FloorRing K] {v : K}

variable {n : ℕ}

theorem stream_eq_none_of_fr_eq_zero {ifp_n : GenContFract.IntFractPair K}
    (stream_nth_eq : GenContFract.IntFractPair.stream v n = some ifp_n) (nth_fr_eq_zero : ifp_n.fr = 0) :
    GenContFract.IntFractPair.stream v (n + 1) = none := by
  obtain ⟨_, fr⟩ := ifp_n
  change fr = 0 at nth_fr_eq_zero
  simp [GenContFract.IntFractPair.stream, stream_nth_eq, nth_fr_eq_zero]

