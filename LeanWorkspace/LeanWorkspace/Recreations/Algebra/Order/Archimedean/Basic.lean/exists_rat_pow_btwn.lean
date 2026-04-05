import Mathlib

variable {G M R K : Type*}

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

variable [Archimedean K] {x y ε : K}

theorem exists_rat_pow_btwn {n : ℕ} (hn : n ≠ 0) {x y : K} (h : x < y) (hy : 0 < y) :
    ∃ q : ℚ, 0 < q ∧ x < (q : K) ^ n ∧ (q : K) ^ n < y := by
  obtain ⟨q₂, hx₂, hy₂⟩ := exists_rat_btwn (max_lt h hy)
  obtain ⟨q₁, hx₁, hq₁₂⟩ := exists_rat_btwn hx₂
  have : (0 : K) < q₂ := (le_max_right _ _).trans_lt hx₂
  norm_cast at hq₁₂ this
  obtain ⟨q, hq, hq₁, hq₂⟩ := exists_pow_btwn hn hq₁₂ this
  refine ⟨q, hq, (le_max_left _ _).trans_lt <| hx₁.trans ?_, hy₂.trans' ?_⟩ <;> assumption_mod_cast

