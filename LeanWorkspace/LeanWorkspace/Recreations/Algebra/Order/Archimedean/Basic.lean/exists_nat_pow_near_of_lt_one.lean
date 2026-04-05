import Mathlib

variable {G M R K : Type*}

variable [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] [Archimedean K] {x y ε : K}

variable [ExistsAddOfLE K]

theorem exists_nat_pow_near_of_lt_one (xpos : 0 < x) (hx : x ≤ 1) (ypos : 0 < y) (hy : y < 1) :
    ∃ n : ℕ, y ^ (n + 1) < x ∧ x ≤ y ^ n := by
  rcases exists_nat_pow_near (one_le_inv_iff₀.2 ⟨xpos, hx⟩) (one_lt_inv_iff₀.2 ⟨ypos, hy⟩) with
    ⟨n, hn, h'n⟩
  refine ⟨n, ?_, ?_⟩
  · rwa [inv_pow, inv_lt_inv₀ xpos (pow_pos ypos _)] at h'n
  · rwa [inv_pow, inv_le_inv₀ (pow_pos ypos _) xpos] at hn

