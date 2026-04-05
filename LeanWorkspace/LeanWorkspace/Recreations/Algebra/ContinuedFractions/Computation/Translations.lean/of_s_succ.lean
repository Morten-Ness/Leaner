import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [FloorRing K] {v : K}

variable {n : ℕ}

variable [IsStrictOrderedRing K]

theorem of_s_succ (n : ℕ) : (of v).s.get? (n + 1) = (of (fract v)⁻¹).s.get? n := by
  rcases eq_or_ne (fract v) 0 with h | h
  · obtain ⟨a, rfl⟩ : ∃ a : ℤ, v = a := ⟨⌊v⌋, eq_of_sub_eq_zero h⟩
    rw [fract_intCast, inv_zero, GenContFract.of_s_of_int, ← cast_zero, GenContFract.of_s_of_int,
      Stream'.Seq.get?_nil, Stream'.Seq.get?_nil]
  rcases eq_or_ne ((of (fract v)⁻¹).s.get? n) none with h₁ | h₁
  · rwa [h₁, ← terminatedAt_iff_s_none,
      GenContFract.of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none, GenContFract.IntFractPair.stream_succ h, ←
      GenContFract.of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none, terminatedAt_iff_s_none]
  · obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.mp h₁
    obtain ⟨p', hp'₁, _⟩ := exists_succ_get?_stream_of_gcf_of_get?_eq_some hp
    have Hp := GenContFract.get?_of_eq_some_of_succ_get?_intFractPair_stream hp'₁
    rw [← GenContFract.IntFractPair.stream_succ h] at hp'₁
    rw [Hp, GenContFract.get?_of_eq_some_of_succ_get?_intFractPair_stream hp'₁]

