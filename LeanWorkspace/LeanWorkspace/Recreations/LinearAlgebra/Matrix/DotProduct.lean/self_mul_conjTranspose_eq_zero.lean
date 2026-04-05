import Mathlib

variable {m n p R : Type*}

variable [Fintype m] [Fintype n] [Fintype p]

variable [PartialOrder R] [NonUnitalRing R] [StarRing R] [StarOrderedRing R]

variable [NoZeroDivisors R]

theorem self_mul_conjTranspose_eq_zero {m} {A : Matrix m n R} : A * Aᴴ = 0 ↔ A = 0 := ⟨fun h => Matrix.ext fun i j =>
    (congr_fun <| dotProduct_self_star_eq_zero.1 <| Matrix.ext_iff.2 h i i) j,
  fun h => h ▸ Matrix.zero_mul _⟩

