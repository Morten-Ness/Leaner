import Mathlib

variable {K : Type*} {v : K} {n : ℕ} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

theorem of_one_le_get?_partDen {b : K}
    (nth_partDen_eq : (of v).partDens.get? n = some b) : 1 ≤ b := by
  obtain ⟨gp_n, nth_s_eq, ⟨-⟩⟩ : ∃ gp_n, (of v).s.get? n = some gp_n ∧ gp_n.b = b :=
    exists_s_b_of_partDen nth_partDen_eq
  obtain ⟨ifp_n, succ_nth_stream_eq, ifp_n_b_eq_gp_n_b⟩ :
      ∃ ifp, IntFractPair.stream v (n + 1) = some ifp ∧ (ifp.b : K) = gp_n.b :=
    IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some nth_s_eq
  rw [← ifp_n_b_eq_gp_n_b]
  exact mod_cast IntFractPair.one_le_succ_nth_stream_b succ_nth_stream_eq

