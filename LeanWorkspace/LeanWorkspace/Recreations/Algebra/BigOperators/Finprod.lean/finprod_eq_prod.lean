import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

theorem finprod_eq_prod (f : α → M) (hf : HasFiniteMulSupport f) :
    ∏ᶠ i : α, f i = ∏ i ∈ hf.toFinset, f i := by classical rw [finprod_def, dif_pos hf]

