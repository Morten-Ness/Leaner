import Mathlib

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable [NonUnitalNonAssocSemiring R]

theorem sum_range_succ_mul_sum_range_succ (m n : ℕ) (f g : ℕ → R) :
    (∑ i ∈ range (m + 1), f i) * ∑ i ∈ range (n + 1), g i =
      (∑ i ∈ range m, f i) * ∑ i ∈ range n, g i +
        f m * ∑ i ∈ range n, g i + (∑ i ∈ range m, f i) * g n + f m * g n := by
  simp only [add_mul, mul_add, add_assoc, sum_range_succ]

