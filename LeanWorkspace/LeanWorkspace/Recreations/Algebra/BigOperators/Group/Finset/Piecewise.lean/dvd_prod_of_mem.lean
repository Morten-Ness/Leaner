import Mathlib

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem dvd_prod_of_mem (f : ι → M) {a : ι} {s : Finset ι} (ha : a ∈ s) : f a ∣ ∏ i ∈ s, f i := by
  classical
    rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem ha]
    exact dvd_mul_right _ _

