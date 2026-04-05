import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommGroup G] [DecidableEq ι] {f : ι → G}

theorem prod_erase_eq_div {a : ι} (h : a ∈ s) : ∏ x ∈ s.erase a, f x = (∏ x ∈ s, f x) / f a := by
  rw [eq_div_iff_mul_eq', Finset.prod_erase_mul _ _ h]

