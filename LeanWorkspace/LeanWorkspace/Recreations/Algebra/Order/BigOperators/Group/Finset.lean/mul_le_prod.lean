import Mathlib

variable {ι α β M N G k R : Type*}

variable [CommMonoid M] [CommMonoid N] [Preorder N]

variable {f g : ι → N} {s t : Finset ι}

theorem mul_le_prod [MulLeftMono N] {i j : ι} (hf : ∀ i ∈ s, 1 ≤ f i) (hi : i ∈ s) (hj : j ∈ s)
    (hne : i ≠ j) :
    f i * f j ≤ ∏ k ∈ s, f k := calc
    f i * f j = ∏ k ∈ .cons i {j} (by simpa), f k := by rw [prod_cons, prod_singleton]
    _ ≤ ∏ k ∈ s, f k := by
      refine Finset.prod_le_prod_of_subset_of_one_le' ?_ fun k hk _ ↦ hf k hk
      simp [cons_subset, *]

