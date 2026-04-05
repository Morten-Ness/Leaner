import Mathlib

variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]

theorem IsStrictOrderedRing.int_eq_of_mul_mem_Ioo
    {r : R} (hr : 0 < r) {k m : ℤ} (h : r * k ∈ Set.Ioo (r * (m - 1 : ℤ)) (r * (m + 1 : ℤ))) :
    k = m := by
  simpa using int_mem_Icc_of_mul_mem_Ioo hr h

