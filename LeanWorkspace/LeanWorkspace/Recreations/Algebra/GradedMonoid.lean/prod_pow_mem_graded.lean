import Mathlib

variable {ι : Type*}

variable {ι R S : Type*} [SetLike S R] [CommMonoid R] [AddCommMonoid ι]

variable (A : ι → S) [SetLike.GradedMonoid A]

variable {κ : Type*} (i : κ → ι) (g : κ → R) {F : Finset κ}

theorem prod_pow_mem_graded (n : κ → ℕ) (hF : ∀ k ∈ F, g k ∈ A (i k)) :
    ∏ k ∈ F, g k ^ n k ∈ A (∑ k ∈ F, n k • i k) := SetLike.prod_mem_graded A _ _ fun k hk ↦ SetLike.pow_mem_graded _ (hF k hk)

