import Mathlib

variable {ι α β M N G k R : Type*}

theorem apply_union_le_sum [AddCommMonoid β] [Preorder β] [AddLeftMono β]
    {f : Set α → β} (zero : f ∅ = 0) (ih : ∀ {s t}, f (s ∪ t) ≤ f s + f t)
    {s : ι → Set α} (t : Finset ι) :
    f (⋃ i ∈ t, s i) ≤ ∑ i ∈ t, f (s i) := Finset.sup_set_eq_biUnion t s ▸ Finset.apply_sup_le_sum t zero (by simpa)

