import Mathlib

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

variable (v : K) (n : ℕ)

theorem exists_rat_eq_of_terminates (terminates : (of v).Terminates) : ∃ q : ℚ, v = ↑q := by
  obtain ⟨n, v_eq_conv⟩ : ∃ n, v = (of v).convs n := of_correctness_of_terminates terminates
  obtain ⟨q, conv_eq_q⟩ : ∃ q : ℚ, (of v).convs n = (↑q : K) := GenContFract.exists_rat_eq_nth_conv v n
  have : v = (↑q : K) := Eq.trans v_eq_conv conv_eq_q
  use q, this

