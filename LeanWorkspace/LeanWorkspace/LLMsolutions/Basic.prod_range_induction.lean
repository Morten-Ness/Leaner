import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_range_induction (f s : ℕ → M) (base : s 0 = 1)
    (n : ℕ) (step : ∀ k < n, s (k + 1) = s k * f k) :
    ∏ k ∈ Finset.range n, f k = s n := by
  induction' n with n ih
  · simp [base]
  · have hstep : s (n + 1) = s n * f n := step n (Nat.lt_succ_self n)
    have ih' : ∏ k ∈ Finset.range n, f k = s n := by
      apply ih
      intro k hk
      exact step k (Nat.lt_trans hk (Nat.lt_succ_self n))
    calc
      ∏ k ∈ Finset.range (n + 1), f k
          = (∏ k ∈ Finset.range n, f k) * f n := by
              rw [Finset.prod_range_succ]
      _ = s n * f n := by rw [ih']
      _ = s (n + 1) := hstep.symm
