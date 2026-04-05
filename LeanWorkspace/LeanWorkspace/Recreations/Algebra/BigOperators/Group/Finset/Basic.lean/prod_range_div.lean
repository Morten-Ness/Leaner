import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommGroup G] [DecidableEq ι] {f : ι → G}

theorem prod_range_div (f : ℕ → G) (n : ℕ) : (∏ i ∈ range n, f (i + 1) / f i) = f n / f 0 := by
  apply Finset.prod_range_induction <;> simp

