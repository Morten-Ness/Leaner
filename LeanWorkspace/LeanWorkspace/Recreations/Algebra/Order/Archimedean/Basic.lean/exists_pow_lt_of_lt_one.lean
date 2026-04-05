import Mathlib

variable {G M R K : Type*}

variable [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] [Archimedean K] {x y ε : K}

variable [ExistsAddOfLE K]

theorem exists_pow_lt_of_lt_one (hx : 0 < x) (hy : y < 1) : ∃ n : ℕ, y ^ n < x := by
  by_cases! y_pos : y ≤ 0
  · use 1
    simp only [pow_one]
    exact y_pos.trans_lt hx
  rcases pow_unbounded_of_one_lt x⁻¹ ((one_lt_inv₀ y_pos).2 hy) with ⟨q, hq⟩
  exact ⟨q, by rwa [inv_pow, inv_lt_inv₀ hx (pow_pos y_pos _)] at hq⟩

