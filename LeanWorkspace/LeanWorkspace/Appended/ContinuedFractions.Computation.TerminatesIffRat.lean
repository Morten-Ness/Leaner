import Mathlib

section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

variable {q : ℚ} {n : ℕ}

theorem of_inv_fr_num_lt_num_of_pos (q_pos : 0 < q) : (GenContFract.IntFractPair.of q⁻¹).fr.num < q.num := Rat.fract_inv_num_lt_num_of_pos q_pos

end
