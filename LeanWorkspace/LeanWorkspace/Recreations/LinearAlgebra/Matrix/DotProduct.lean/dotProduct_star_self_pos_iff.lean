import Mathlib

variable {m n p R : Type*}

variable [Fintype m] [Fintype n] [Fintype p]

variable [PartialOrder R] [NonUnitalRing R] [StarRing R] [StarOrderedRing R]

variable [NoZeroDivisors R]

theorem dotProduct_star_self_pos_iff {v : n → R} :
    0 < star v ⬝ᵥ v ↔ v ≠ 0 := by
  nontriviality R
  refine (Fintype.sum_pos_iff_of_nonneg fun i => star_mul_self_nonneg _).trans ?_
  simp_rw [Pi.lt_def, Function.ne_iff, Pi.zero_apply]
  refine (and_iff_right fun i => star_mul_self_nonneg (v i)).trans <| exists_congr fun i => ?_
  constructor
  · rintro h hv
    simp [hv] at h
  · exact (star_mul_self_pos <| .of_ne_zero ·)

