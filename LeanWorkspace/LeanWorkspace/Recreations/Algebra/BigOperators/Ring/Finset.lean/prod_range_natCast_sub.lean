import Mathlib

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable [CommRing R]

theorem prod_range_natCast_sub (n k : ℕ) :
    ∏ i ∈ range k, (n - i : R) = (∏ i ∈ range k, (n - i) : ℕ) := by
  rw [Finset.prod_natCast]
  rcases le_or_gt k n with hkn | hnk
  · exact prod_congr rfl fun i hi => (Nat.cast_sub <| (mem_range.1 hi).le.trans hkn).symm
  · rw [← mem_range] at hnk
    rw [prod_eq_zero hnk, prod_eq_zero hnk] <;> simp

