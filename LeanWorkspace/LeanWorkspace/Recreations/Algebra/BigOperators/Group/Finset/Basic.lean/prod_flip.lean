import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_flip {n : ℕ} (f : ℕ → M) :
    (∏ r ∈ range (n + 1), f (n - r)) = ∏ k ∈ range (n + 1), f k := by
  induction n with
  | zero => rw [Finset.prod_range_one, Finset.prod_range_one]
  | succ n ih =>
    rw [Finset.prod_range_succ', Finset.prod_range_succ _ (Nat.succ n)]
    simp [← ih]

