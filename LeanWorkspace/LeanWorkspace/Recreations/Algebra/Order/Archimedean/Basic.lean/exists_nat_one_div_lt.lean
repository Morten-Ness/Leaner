import Mathlib

variable {G M R K : Type*}

variable [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] [Archimedean K] {x y ε : K}

theorem exists_nat_one_div_lt (hε : 0 < ε) : ∃ n : ℕ, 1 / (n + 1 : K) < ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
  use n
  rw [div_lt_iff₀, ← div_lt_iff₀' hε]
  · apply hn.trans
    simp [zero_lt_one]
  · exact n.cast_add_one_pos

