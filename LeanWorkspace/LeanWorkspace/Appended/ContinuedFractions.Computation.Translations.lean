import Mathlib

section

variable {K : Type*} [DivisionRing K] [LinearOrder K] [FloorRing K] {v : K}

variable {n : ℕ}

theorem exists_succ_nth_stream_of_fr_zero {ifp_succ_n : GenContFract.IntFractPair K}
    (stream_succ_nth_eq : GenContFract.IntFractPair.stream v (n + 1) = some ifp_succ_n)
    (succ_nth_fr_eq_zero : ifp_succ_n.fr = 0) :
    ∃ ifp_n : GenContFract.IntFractPair K, GenContFract.IntFractPair.stream v n = some ifp_n ∧ ifp_n.fr⁻¹ = ⌊ifp_n.fr⁻¹⌋ := by
  -- get the witness from `GenContFract.IntFractPair.succ_nth_stream_eq_some_iff` and prove that it has the additional
  -- properties
  rcases GenContFract.IntFractPair.succ_nth_stream_eq_some_iff.mp stream_succ_nth_eq with
    ⟨ifp_n, seq_nth_eq, _, rfl⟩
  refine ⟨ifp_n, seq_nth_eq, ?_⟩
  simpa only [GenContFract.IntFractPair.of, Int.fract, sub_eq_zero] using succ_nth_fr_eq_zero

end

section

variable {K : Type*} [DivisionRing K] [LinearOrder K] [FloorRing K] {v : K}

variable {n : ℕ}

theorem stream_eq_none_of_fr_eq_zero {ifp_n : GenContFract.IntFractPair K}
    (stream_nth_eq : GenContFract.IntFractPair.stream v n = some ifp_n) (nth_fr_eq_zero : ifp_n.fr = 0) :
    GenContFract.IntFractPair.stream v (n + 1) = none := by
  obtain ⟨_, fr⟩ := ifp_n
  change fr = 0 at nth_fr_eq_zero
  simp [GenContFract.IntFractPair.stream, stream_nth_eq, nth_fr_eq_zero]

end

section

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

end

section

variable {K : Type*} [DivisionRing K] [LinearOrder K] [FloorRing K] {v : K}

variable {n : ℕ}

theorem stream_succ_of_int [IsStrictOrderedRing K] (a : ℤ) (n : ℕ) :
    GenContFract.IntFractPair.stream (a : K) (n + 1) = none := by
  induction n with
  | zero =>
    refine GenContFract.IntFractPair.stream_eq_none_of_fr_eq_zero (GenContFract.IntFractPair.stream_zero (a : K)) ?_
    simp only [GenContFract.IntFractPair.of, Int.fract_intCast]
  | succ n ih => exact GenContFract.IntFractPair.succ_nth_stream_eq_none_iff.mpr (Or.inl ih)

end

section

variable {K : Type*} [DivisionRing K] [LinearOrder K] [FloorRing K] {v : K}

variable {n : ℕ}

theorem stream_succ_of_some {p : GenContFract.IntFractPair K} (h : GenContFract.IntFractPair.stream v n = some p)
    (h' : p.fr ≠ 0) : GenContFract.IntFractPair.stream v (n + 1) = some (GenContFract.IntFractPair.of p.fr⁻¹) := GenContFract.IntFractPair.succ_nth_stream_eq_some_iff.mpr ⟨p, h, h', rfl⟩

end

section

variable {K : Type*} [DivisionRing K] [LinearOrder K] [FloorRing K] {v : K}

variable {n : ℕ}

theorem succ_nth_stream_eq_none_iff :
    GenContFract.IntFractPair.stream v (n + 1) = none ↔
      GenContFract.IntFractPair.stream v n = none ∨ ∃ ifp, GenContFract.IntFractPair.stream v n = some ifp ∧ ifp.fr = 0 := by
  rw [GenContFract.IntFractPair.stream]
  cases GenContFract.IntFractPair.stream v n <;> simp [imp_false]

end

section

variable {K : Type*} [DivisionRing K] [LinearOrder K] [FloorRing K] {v : K}

variable {n : ℕ}

theorem succ_nth_stream_eq_some_iff {ifp_succ_n : GenContFract.IntFractPair K} :
    GenContFract.IntFractPair.stream v (n + 1) = some ifp_succ_n ↔
      ∃ ifp_n : GenContFract.IntFractPair K,
        GenContFract.IntFractPair.stream v n = some ifp_n ∧
          ifp_n.fr ≠ 0 ∧ GenContFract.IntFractPair.of ifp_n.fr⁻¹ = ifp_succ_n := by
  simp [GenContFract.IntFractPair.stream, ite_eq_iff, Option.bind_eq_some_iff]

end
