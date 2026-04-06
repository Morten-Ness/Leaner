FAIL
import Mathlib

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

variable {q : ℚ} {n : ℕ}

theorem of_inv_fr_num_lt_num_of_pos (q_pos : 0 < q) : (GenContFract.IntFractPair.of q⁻¹).fr.num < q.num := by
  simpa [GenContFract.IntFractPair.of, Rat.floor_intRat_inv_num_den, q_pos]
    using Rat.num_den_mk q.num q.den_nz
