import Mathlib

variable {α β m n o : Type*} {m' n' : α → Type*}

variable {R : Type v} {M N : Matrix m m R} {b : m → α}

variable [LinearOrder α]

theorem BlockTriangular.mul [Fintype m] [NonUnitalNonAssocSemiring R]
    {M N : Matrix m m R} (hM : Matrix.BlockTriangular M b)
    (hN : Matrix.BlockTriangular N b) : Matrix.BlockTriangular (M * N) b := by
  intro i j hij
  apply Finset.sum_eq_zero
  intro k _
  by_cases! hki : b k < b i
  · simp_rw [hM hki, zero_mul]
  · simp_rw [hN (lt_of_lt_of_le hij hki), mul_zero]

