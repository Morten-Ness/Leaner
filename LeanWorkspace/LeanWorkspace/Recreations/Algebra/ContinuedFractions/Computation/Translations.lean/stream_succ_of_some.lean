import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [FloorRing K] {v : K}

variable {n : ℕ}

theorem stream_succ_of_some {p : GenContFract.IntFractPair K} (h : GenContFract.IntFractPair.stream v n = some p)
    (h' : p.fr ≠ 0) : GenContFract.IntFractPair.stream v (n + 1) = some (GenContFract.IntFractPair.of p.fr⁻¹) := GenContFract.IntFractPair.succ_nth_stream_eq_some_iff.mpr ⟨p, h, h', rfl⟩

