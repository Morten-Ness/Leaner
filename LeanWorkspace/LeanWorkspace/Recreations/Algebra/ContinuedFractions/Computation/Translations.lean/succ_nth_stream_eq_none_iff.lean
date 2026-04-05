import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [FloorRing K] {v : K}

variable {n : ℕ}

theorem succ_nth_stream_eq_none_iff :
    GenContFract.IntFractPair.stream v (n + 1) = none ↔
      GenContFract.IntFractPair.stream v n = none ∨ ∃ ifp, GenContFract.IntFractPair.stream v n = some ifp ∧ ifp.fr = 0 := by
  rw [GenContFract.IntFractPair.stream]
  cases GenContFract.IntFractPair.stream v n <;> simp [imp_false]

