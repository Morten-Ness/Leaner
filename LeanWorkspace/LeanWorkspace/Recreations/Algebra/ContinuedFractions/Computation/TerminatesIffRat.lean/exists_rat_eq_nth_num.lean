import Mathlib

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

variable (v : K) (n : ℕ)

theorem exists_rat_eq_nth_num : ∃ q : ℚ, (of v).nums n = (q : K) := by
  rcases GenContFract.exists_gcf_pair_rat_eq_nth_conts v n with ⟨⟨a, _⟩, nth_cont_eq⟩
  use a
  simp [num_eq_conts_a, nth_cont_eq]

