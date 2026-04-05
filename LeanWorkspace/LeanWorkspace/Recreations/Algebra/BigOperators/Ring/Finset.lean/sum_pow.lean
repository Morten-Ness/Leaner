import Mathlib

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable {ι κ R : Type*} [Fintype ι] [Fintype κ] [CommSemiring R]

theorem sum_pow (f : ι → R) (n : ℕ) : (∑ a, f a) ^ n = ∑ p : Fin n → ι, ∏ i, f (p i) := by
  simp [Finset.sum_pow']

