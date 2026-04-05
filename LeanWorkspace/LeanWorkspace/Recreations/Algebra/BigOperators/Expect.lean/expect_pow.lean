import Mathlib

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [CommSemiring M] [Module ℚ≥0 M] [IsScalarTower ℚ≥0 M M] [SMulCommClass ℚ≥0 M M]

theorem expect_pow (s : Finset ι) (f : ι → M) (n : ℕ) :
    (𝔼 i ∈ s, f i) ^ n = 𝔼 p ∈ Fintype.piFinset fun _ : Fin n ↦ s, ∏ i, f (p i) := by
  classical
  rw [expect, smul_pow, sum_pow', expect, Fintype.card_piFinset_const, inv_pow, Nat.cast_pow]

