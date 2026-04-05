import Mathlib

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

variable {q : ℚ} {n : ℕ}

theorem exists_nth_stream_eq_none_of_rat (q : ℚ) : ∃ n : ℕ, GenContFract.IntFractPair.stream q n = none := by
  let fract_q_num := (Int.fract q).num; let n := fract_q_num.natAbs + 1
  rcases stream_nth_eq : GenContFract.IntFractPair.stream q n with ifp | ifp
  · use n, stream_nth_eq
  · -- arrive at a contradiction since the numerator decreased num + 1 times but every fractional
    -- value is nonnegative.
    have ifp_fr_num_le_q_fr_num_sub_n : ifp.fr.num ≤ fract_q_num - n :=
      GenContFract.IntFractPair.stream_nth_fr_num_le_fr_num_sub_n_rat stream_nth_eq
    have : fract_q_num - n = -1 := by
      have : 0 ≤ fract_q_num := Rat.num_nonneg.mpr (Int.fract_nonneg q)
      simp only [n, Nat.cast_add, Int.natAbs_of_nonneg this, Nat.cast_one,
        sub_add_eq_sub_sub_swap, sub_right_comm, sub_self, zero_sub]
    have : 0 ≤ ifp.fr := (nth_stream_fr_nonneg_lt_one stream_nth_eq).left
    have : 0 ≤ ifp.fr.num := Rat.num_nonneg.mpr this
    lia

