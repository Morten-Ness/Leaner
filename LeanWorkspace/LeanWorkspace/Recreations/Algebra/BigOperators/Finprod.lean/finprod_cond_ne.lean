import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

theorem finprod_cond_ne (f : α → M) (a : α) [DecidableEq α] (hf : HasFiniteMulSupport f) :
    (∏ᶠ (i) (_ : i ≠ a), f i) = ∏ i ∈ hf.toFinset.erase a, f i := by
  apply finprod_cond_eq_prod_of_cond_iff
  intro x hx
  rw [Finset.mem_erase, Finite.mem_toFinset, mem_mulSupport]
  grind

