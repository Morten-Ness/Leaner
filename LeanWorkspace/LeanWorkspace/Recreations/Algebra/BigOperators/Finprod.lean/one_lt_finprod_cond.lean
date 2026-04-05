import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem one_lt_finprod_cond {M : Type*} [CommMonoid M] [PartialOrder M] [IsOrderedCancelMonoid M]
    {f : ι → M} {p : ι → Prop} (h : ∀ i, p i → 1 ≤ f i) (h' : ∃ i, p i ∧ 1 < f i)
    (hf : (mulSupport f ∩ {i | p i}).Finite) : 1 < ∏ᶠ (i) (_ : p i), f i := by
  rw [finprod_cond_eq_prod_of_cond_iff (t := hf.toFinset)]
  · apply Finset.one_lt_prod'
    · simp +contextual [h]
    · aesop
  · simp +contextual

