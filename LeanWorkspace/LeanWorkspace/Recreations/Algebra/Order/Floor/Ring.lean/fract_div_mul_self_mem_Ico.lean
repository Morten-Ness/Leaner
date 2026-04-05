import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

variable {k : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k] [FloorRing k] {b : k}

theorem fract_div_mul_self_mem_Ico (a b : k) (ha : 0 < a) : fract (b / a) * a ∈ Ico 0 a := ⟨(mul_nonneg_iff_of_pos_right ha).2 (Int.fract_nonneg (b / a)),
    (mul_lt_iff_lt_one_left ha).2 (Int.fract_lt_one (b / a))⟩

