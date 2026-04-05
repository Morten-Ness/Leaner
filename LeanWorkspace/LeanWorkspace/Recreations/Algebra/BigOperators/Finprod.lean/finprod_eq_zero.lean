import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_eq_zero {M₀ : Type*} [CommMonoidWithZero M₀] (f : α → M₀) (x : α) (hx : f x = 0)
    (hf : HasFiniteMulSupport f) : ∏ᶠ x, f x = 0 := by
  nontriviality
  rw [finprod_eq_prod f hf]
  refine Finset.prod_eq_zero (hf.mem_toFinset.2 ?_) hx
  simp [hx]

