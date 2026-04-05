import Mathlib

open scoped BigOperators Pointwise NNRat

variable {ι α R : Type*}

variable [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [Module ℚ≥0 α] [PosSMulMono ℚ≥0 α]

theorem abs_expect_le (s : Finset ι) (f : ι → α) : |𝔼 i ∈ s, f i| ≤ 𝔼 i ∈ s, |f i| := Finset.le_expect_of_subadditive abs_zero abs_add_le (fun _ ↦ abs_nnqsmul _)

