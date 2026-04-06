FAIL
import Mathlib

variable {ι : Type*}

variable {ι R S : Type*} [SetLike S R] [CommMonoid R] [AddCommMonoid ι]

variable (A : ι → S) [SetLike.GradedMonoid A]

variable {κ : Type*} (i : κ → ι) (g : κ → R) {F : Finset κ}

theorem prod_pow_mem_graded (n : κ → ℕ) (hF : ∀ k ∈ F, g k ∈ A (i k)) :
    ∏ k ∈ F, g k ^ n k ∈ A (∑ k ∈ F, n k • i k) := by
  classical
  simpa only [Finset.prod_pow_eq_pow_sum, Finset.sum_map] using
    SetLike.mem_gradedMonoid_finset_prod_pow (A := A) (s := F) (ι := i) (r := g) n hF
