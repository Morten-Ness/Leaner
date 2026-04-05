import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [FloorRing K] {v : K}

variable {n : ℕ}

theorem get?_of_eq_some_of_succ_get?_intFractPair_stream {ifp_succ_n : IntFractPair K}
    (stream_succ_nth_eq : IntFractPair.stream v (n + 1) = some ifp_succ_n) :
    (of v).s.get? n = some ⟨1, ifp_succ_n.b⟩ := by
  unfold of IntFractPair.seq1
  simp [Stream'.Seq.map_tail, Stream'.Seq.get?_tail, Stream'.Seq.map_get?, stream_succ_nth_eq]

