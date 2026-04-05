import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem one_lt_finprod {M : Type*} [CommMonoid M] [PartialOrder M] [IsOrderedCancelMonoid M]
    {f : ι → M}
    (h : ∀ i, 1 ≤ f i) (h' : ∃ i, 1 < f i) (hf : HasFiniteMulSupport f) : 1 < ∏ᶠ i, f i := by
  rw [← finprod_mem_univ]
  apply one_lt_finprod_cond <;> simpa

