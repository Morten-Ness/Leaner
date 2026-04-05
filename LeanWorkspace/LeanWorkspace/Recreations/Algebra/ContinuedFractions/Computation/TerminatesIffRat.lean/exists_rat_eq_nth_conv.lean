import Mathlib

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

variable (v : K) (n : ℕ)

theorem exists_rat_eq_nth_conv : ∃ q : ℚ, (of v).convs n = (q : K) := by
  rcases GenContFract.exists_rat_eq_nth_num v n with ⟨Aₙ, nth_num_eq⟩
  rcases GenContFract.exists_rat_eq_nth_den v n with ⟨Bₙ, nth_den_eq⟩
  use Aₙ / Bₙ
  simp [nth_num_eq, nth_den_eq, conv_eq_num_div_den]

