FAIL
import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [FloorRing K] {v : K}

variable {n : ℕ}

theorem stream_eq_none_of_fr_eq_zero {ifp_n : GenContFract.IntFractPair K}
    (stream_nth_eq : GenContFract.IntFractPair.stream v n = some ifp_n) (nth_fr_eq_zero : ifp_n.fr = 0) :
    GenContFract.IntFractPair.stream v (n + 1) = none := by
  rcases n with _ | n
  · simp only [Nat.zero_eq, Nat.zero_add] at stream_nth_eq ⊢
    rw [GenContFract.IntFractPair.stream]
    simp [stream_nth_eq, nth_fr_eq_zero]
  · rw [GenContFract.IntFractPair.stream_succ] at stream_nth_eq ⊢
    split at stream_nth_eq
    · rename_i ifp
      cases h : ifp.fr = 0
      · simp [h] at stream_nth_eq
      · simp [h] at stream_nth_eq
    · simp at stream_nth_eq
