import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [FloorRing K] {v : K}

variable {n : ℕ}

theorem succ_nth_stream_eq_none_iff :
    GenContFract.IntFractPair.stream v (n + 1) = none ↔
      GenContFract.IntFractPair.stream v n = none ∨ ∃ ifp, GenContFract.IntFractPair.stream v n = some ifp ∧ ifp.fr = 0 := by
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    GenContFract.IntFractPair.succ_nth_stream_eq_none_iff (v := v) (n := n)
