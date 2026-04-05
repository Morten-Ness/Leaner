import Mathlib

variable {G M R K : Type*}

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

variable [Archimedean K] {x y ε : K}

theorem exists_rat_btwn {x y : K} (h : x < y) : ∃ q : ℚ, x < q ∧ q < y := by
  obtain ⟨n, nh⟩ := exists_nat_gt (y - x)⁻¹
  obtain ⟨z, zh, zh'⟩ := exists_div_btwn h nh
  refine ⟨(z : ℚ) / n, ?_, ?_⟩ <;> simpa

