import Mathlib

open scoped BigOperators Pointwise NNRat

variable {ι α R : Type*}

variable [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R] [Module ℚ≥0 R]
  [PosSMulMono ℚ≥0 R]

theorem expect_mul_sq_le_sq_mul_sq (s : Finset ι) (f g : ι → R) :
    (𝔼 i ∈ s, f i * g i) ^ 2 ≤ (𝔼 i ∈ s, f i ^ 2) * 𝔼 i ∈ s, g i ^ 2 := by
  simp only [expect, smul_pow, inv_pow, smul_mul_smul_comm, ← sq]
  gcongr
  exact sum_mul_sq_le_sq_mul_sq ..

