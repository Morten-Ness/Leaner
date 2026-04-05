import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_range_succ_comm (f : ℕ → M) (n : ℕ) :
    (∏ x ∈ range (n + 1), f x) = f n * ∏ x ∈ range n, f x := by
  rw [range_add_one, Finset.prod_insert notMem_range_self]

