import Mathlib

section

variable {ι : Type*}

variable {R : Type*}

variable {S : Type*} [SetLike S R] [Monoid R] [AddMonoid ι]

variable {A : ι → S} [SetLike.GradedMonoid A]

theorem list_prod_ofFn_mem_graded {n} (i : Fin n → ι) (r : Fin n → R) (h : ∀ j, r j ∈ A (i j)) :
    (List.ofFn r).prod ∈ A (List.ofFn i).sum := by
  rw [List.ofFn_eq_map, List.ofFn_eq_map]
  exact SetLike.list_prod_map_mem_graded _ _ _ fun _ _ => h _

end

section

variable {ι : Type*}

variable {ι R S : Type*} [SetLike S R] [CommMonoid R] [AddCommMonoid ι]

variable (A : ι → S) [SetLike.GradedMonoid A]

variable {κ : Type*} (i : κ → ι) (g : κ → R) {F : Finset κ}

theorem prod_pow_mem_graded (n : κ → ℕ) (hF : ∀ k ∈ F, g k ∈ A (i k)) :
    ∏ k ∈ F, g k ^ n k ∈ A (∑ k ∈ F, n k • i k) := SetLike.prod_mem_graded A _ _ fun k hk ↦ SetLike.pow_mem_graded _ (hF k hk)

end
