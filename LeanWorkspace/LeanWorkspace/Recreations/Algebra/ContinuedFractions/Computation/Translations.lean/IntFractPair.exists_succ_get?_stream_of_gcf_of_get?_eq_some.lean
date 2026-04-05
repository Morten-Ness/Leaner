import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [FloorRing K] {v : K}

variable {n : ℕ}

theorem IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some {gp_n : Pair K}
    (s_nth_eq : (of v).s.get? n = some gp_n) :
    ∃ ifp : IntFractPair K, IntFractPair.stream v (n + 1) = some ifp ∧ (ifp.b : K) = gp_n.b := by
  obtain ⟨ifp, stream_succ_nth_eq, gp_n_eq⟩ :
    ∃ ifp, IntFractPair.stream v (n + 1) = some ifp ∧ Pair.mk 1 (ifp.b : K) = gp_n := by
    unfold of IntFractPair.seq1 at s_nth_eq
    simpa [Stream'.Seq.get?_tail, Stream'.Seq.map_get?] using s_nth_eq
  cases gp_n_eq
  simp_all only [Option.some.injEq, exists_eq_left']

