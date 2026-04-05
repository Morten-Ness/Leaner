import Mathlib

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable [CommSemiring R]

variable [DecidableEq ι]

theorem sum_pow' (s : Finset κ) (f : κ → R) (n : ℕ) :
    (∑ a ∈ s, f a) ^ n = ∑ p ∈ piFinset fun _i : Fin n ↦ s, ∏ i, f (p i) := by
  convert @Finset.prod_univ_sum (Fin n) _ _ _ _ _ (fun _i ↦ s) fun _i d ↦ f d; simp

