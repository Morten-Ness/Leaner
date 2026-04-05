import Mathlib

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

variable {q : ℚ} {n : ℕ}

theorem stream_succ_nth_fr_num_lt_nth_fr_num_rat {ifp_n ifp_succ_n : GenContFract.IntFractPair ℚ}
    (stream_nth_eq : GenContFract.IntFractPair.stream q n = some ifp_n)
    (stream_succ_nth_eq : GenContFract.IntFractPair.stream q (n + 1) = some ifp_succ_n) :
    ifp_succ_n.fr.num < ifp_n.fr.num := by
  obtain ⟨ifp_n', stream_nth_eq', ifp_n_fract_ne_zero, GenContFract.IntFractPair.of_eq_ifp_succ_n⟩ :
    ∃ ifp_n',
      GenContFract.IntFractPair.stream q n = some ifp_n' ∧
        ifp_n'.fr ≠ 0 ∧ GenContFract.IntFractPair.of ifp_n'.fr⁻¹ = ifp_succ_n :=
    succ_nth_stream_eq_some_iff.mp stream_succ_nth_eq
  have : ifp_n = ifp_n' := by injection Eq.trans stream_nth_eq.symm stream_nth_eq'
  cases this
  rw [← GenContFract.IntFractPair.of_eq_ifp_succ_n]
  obtain ⟨zero_le_ifp_n_fract, _⟩ := nth_stream_fr_nonneg_lt_one stream_nth_eq
  have : 0 < ifp_n.fr := lt_of_le_of_ne zero_le_ifp_n_fract <| ifp_n_fract_ne_zero.symm
  exact GenContFract.IntFractPair.of_inv_fr_num_lt_num_of_pos this

