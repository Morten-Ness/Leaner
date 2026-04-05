import Mathlib

variable {G M R K : Type*}

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

variable [Archimedean K] {x y ε : K}

theorem exists_div_btwn {x y : K} {n : ℕ} (h : x < y) (nh : (y - x)⁻¹ < n) :
    ∃ z : ℤ, x < (z : K) / n ∧ (z : K) / n < y := by
  obtain ⟨z, zh⟩ := exists_floor (x * n)
  refine ⟨z + 1, ?_⟩
  have n0' := (inv_pos.2 (sub_pos.2 h)).trans nh
  rw [div_lt_iff₀ n0']
  refine ⟨(lt_div_iff₀ n0').2 <| (lt_iff_lt_of_le_iff_le (zh _)).1 (lt_add_one _), ?_⟩
  rw [Int.cast_add, Int.cast_one]
  grw [(zh _).1 le_rfl]
  rwa [← lt_sub_iff_add_lt', ← sub_mul, ← div_lt_iff₀' (sub_pos.2 h), one_div]

