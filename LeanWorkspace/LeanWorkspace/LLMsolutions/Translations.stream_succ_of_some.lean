FAIL
import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [FloorRing K] {v : K}

variable {n : ℕ}

theorem stream_succ_of_some {p : GenContFract.IntFractPair K} (h : GenContFract.IntFractPair.stream v n = some p)
    (h' : p.fr ≠ 0) : GenContFract.IntFractPair.stream v (n + 1) = some (GenContFract.IntFractPair.of p.fr⁻¹) := by
  cases n with
  | zero =>
      simp [GenContFract.IntFractPair.stream] at h ⊢
      subst h
      simp [GenContFract.IntFractPair.stream, h']
  | succ n =>
      simp [GenContFract.IntFractPair.stream, h, h']
