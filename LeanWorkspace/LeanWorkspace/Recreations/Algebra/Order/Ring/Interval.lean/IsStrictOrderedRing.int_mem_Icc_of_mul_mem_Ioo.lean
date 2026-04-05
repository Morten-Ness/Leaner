import Mathlib

variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]

theorem IsStrictOrderedRing.int_mem_Icc_of_mul_mem_Ioo
    {r : R} (hr : 0 < r) {k m n : ℤ} (h : r * k ∈ Set.Ioo (r * (m - 1 : ℤ)) (r * (n + 1 : ℤ))) :
    k ∈ Finset.Icc m n := by
  simp only [Set.mem_Ioo, mul_lt_mul_iff_right₀ hr, Int.cast_lt] at h
  grind [Int.lt_iff_add_one_le]

