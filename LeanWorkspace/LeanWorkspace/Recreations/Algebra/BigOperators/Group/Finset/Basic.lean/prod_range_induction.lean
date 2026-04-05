import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_range_induction (f s : ℕ → M) (base : s 0 = 1)
    (n : ℕ) (step : ∀ k < n, s (k + 1) = s k * f k) :
    ∏ k ∈ Finset.range n, f k = s n := by
  induction n with
  | zero => rw [Finset.prod_range_zero, base]
  | succ k hk =>
    rw [Finset.prod_range_succ, step _ (Nat.lt_succ_self _), hk]
    exact fun _ hl ↦ step _ (Nat.lt_succ_of_lt hl)

