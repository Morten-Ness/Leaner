import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_range_succ' (f : ℕ → M) :
    ∀ n : ℕ, (∏ k ∈ range (n + 1), f k) = (∏ k ∈ range n, f (k + 1)) * f 0
  | 0 => Finset.prod_range_succ _ _
  | n + 1 => by rw [Finset.prod_range_succ _ n, mul_right_comm, ← prod_range_succ' _ n, Finset.prod_range_succ]
