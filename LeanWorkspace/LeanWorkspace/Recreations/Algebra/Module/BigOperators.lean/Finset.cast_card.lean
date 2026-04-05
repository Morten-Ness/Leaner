import Mathlib

variable {ι κ α β R M : Type*}

theorem Finset.cast_card [NonAssocSemiring R] (s : Finset α) : (#s : R) = ∑ _ ∈ s, 1 := by
  rw [Finset.sum_const, Nat.smul_one_eq_cast]

