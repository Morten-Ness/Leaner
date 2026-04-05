import Mathlib

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

variable {v : K} {q : ℚ}

theorem coe_of_s_get?_rat_eq (v_eq_q : v = (↑q : K)) (n : ℕ) :
    (((of q).s.get? n).map (Pair.map (↑)) : Option <| Pair K) = (of v).s.get? n := by
  simp only [of, IntFractPair.seq1, Stream'.Seq.map_get?, Stream'.Seq.get?_tail]
  simp only [Stream'.Seq.get?]
  rw [← IntFractPair.coe_stream'_rat_eq v_eq_q]
  rcases succ_nth_stream_eq : IntFractPair.stream q (n + 1) with (_ | ⟨_, _⟩) <;>
    simp [Stream'.map, Stream'.get, succ_nth_stream_eq]

