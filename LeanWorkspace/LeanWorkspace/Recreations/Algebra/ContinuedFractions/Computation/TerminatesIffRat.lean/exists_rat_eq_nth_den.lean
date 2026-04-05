import Mathlib

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

variable (v : K) (n : ℕ)

theorem exists_rat_eq_nth_den : ∃ q : ℚ, (of v).dens n = (q : K) := by
  rcases GenContFract.exists_gcf_pair_rat_eq_nth_conts v n with ⟨⟨_, b⟩, nth_cont_eq⟩
  use b
  simp [den_eq_conts_b, nth_cont_eq]

