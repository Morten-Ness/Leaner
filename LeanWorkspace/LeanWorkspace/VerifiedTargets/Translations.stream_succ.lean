import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [FloorRing K] {v : K}

variable {n : ℕ}

theorem stream_succ (h : Int.fract v ≠ 0) (n : ℕ) :
    GenContFract.IntFractPair.stream v (n + 1) = GenContFract.IntFractPair.stream (Int.fract v)⁻¹ n := by
  induction n with
  | zero =>
    have H : (GenContFract.IntFractPair.of v).fr = Int.fract v := by simp [GenContFract.IntFractPair.of]
    rw [GenContFract.IntFractPair.stream_zero, GenContFract.IntFractPair.stream_succ_of_some (GenContFract.IntFractPair.stream_zero v) (ne_of_eq_of_ne H h), H]
  | succ n ih =>
    rcases eq_or_ne (GenContFract.IntFractPair.stream (Int.fract v)⁻¹ n) none with hnone | hsome
    · rw [hnone] at ih
      rw [GenContFract.IntFractPair.succ_nth_stream_eq_none_iff.mpr (Or.inl hnone),
        GenContFract.IntFractPair.succ_nth_stream_eq_none_iff.mpr (Or.inl ih)]
    · obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.mp hsome
      rw [hp] at ih
      rcases eq_or_ne p.fr 0 with hz | hnz
      · rw [GenContFract.IntFractPair.stream_eq_none_of_fr_eq_zero hp hz, GenContFract.IntFractPair.stream_eq_none_of_fr_eq_zero ih hz]
      · rw [GenContFract.IntFractPair.stream_succ_of_some hp hnz, GenContFract.IntFractPair.stream_succ_of_some ih hnz]

