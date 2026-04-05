import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommGroup G] [DecidableEq ι] {f : ι → G}

theorem eq_prod_range_div (f : ℕ → G) (n : ℕ) : f n = f 0 * ∏ i ∈ range n, f (i + 1) / f i := by
  rw [Finset.prod_range_div, mul_div_cancel]

