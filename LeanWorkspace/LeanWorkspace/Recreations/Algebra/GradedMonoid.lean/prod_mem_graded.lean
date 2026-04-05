import Mathlib

variable {ι : Type*}

variable {ι R S : Type*} [SetLike S R] [CommMonoid R] [AddCommMonoid ι]

variable (A : ι → S) [SetLike.GradedMonoid A]

variable {κ : Type*} (i : κ → ι) (g : κ → R) {F : Finset κ}

theorem prod_mem_graded (hF : ∀ k ∈ F, g k ∈ A (i k)) : ∏ k ∈ F, g k ∈ A (∑ k ∈ F, i k) := by
  classical
  induction F using Finset.induction_on
  · simp [GradedOne.one_mem]
  · case insert j F' hF2 h3 =>
    rw [Finset.prod_insert hF2, Finset.sum_insert hF2]
    apply SetLike.mul_mem_graded (by grind)
    grind

