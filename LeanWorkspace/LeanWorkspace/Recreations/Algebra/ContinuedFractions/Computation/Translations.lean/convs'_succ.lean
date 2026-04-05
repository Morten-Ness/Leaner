import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [FloorRing K] {v : K}

variable {n : ℕ}

variable [IsStrictOrderedRing K]

theorem convs'_succ :
    (of v).convs' (n + 1) = ⌊v⌋ + 1 / (of (fract v)⁻¹).convs' n := by
  rcases eq_or_ne (fract v) 0 with h | h
  · obtain ⟨a, rfl⟩ : ∃ a : ℤ, v = a := ⟨⌊v⌋, eq_of_sub_eq_zero h⟩
    rw [GenContFract.convs'_of_int, fract_intCast, inv_zero, ← cast_zero, GenContFract.convs'_of_int, cast_zero,
      div_zero, add_zero, floor_intCast]
  · rw [convs', GenContFract.of_h_eq_floor, add_right_inj, convs'Aux_succ_some (GenContFract.of_s_head h)]
    exact congr_arg (1 / ·) (by rw [convs', GenContFract.of_h_eq_floor, add_right_inj, GenContFract.of_s_tail])

