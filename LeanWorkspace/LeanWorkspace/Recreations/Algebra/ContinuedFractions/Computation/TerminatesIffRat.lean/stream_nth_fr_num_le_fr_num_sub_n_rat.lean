import Mathlib

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

variable {q : ℚ} {n : ℕ}

theorem stream_nth_fr_num_le_fr_num_sub_n_rat :
    ∀ {ifp_n : GenContFract.IntFractPair ℚ},
      GenContFract.IntFractPair.stream q n = some ifp_n → ifp_n.fr.num ≤ (GenContFract.IntFractPair.of q).fr.num - n := by
  induction n with
  | zero =>
    intro ifp_zero stream_zero_eq
    have : GenContFract.IntFractPair.of q = ifp_zero := by injection stream_zero_eq
    simp [this.symm]
  | succ n IH =>
    intro ifp_succ_n stream_succ_nth_eq
    suffices ifp_succ_n.fr.num + 1 ≤ (GenContFract.IntFractPair.of q).fr.num - n by
      rw [Int.natCast_succ, sub_add_eq_sub_sub]
      solve_by_elim [le_sub_right_of_add_le]
    rcases succ_nth_stream_eq_some_iff.mp stream_succ_nth_eq with ⟨ifp_n, stream_nth_eq, -⟩
    have : ifp_succ_n.fr.num < ifp_n.fr.num :=
      GenContFract.IntFractPair.stream_succ_nth_fr_num_lt_nth_fr_num_rat stream_nth_eq stream_succ_nth_eq
    exact le_trans this (IH stream_nth_eq)

