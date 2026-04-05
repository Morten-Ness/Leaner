import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [AddCommMonoid M] [PartialOrder M] [Sub M] [OrderedSub M] [AddLeftMono M]
  [AddLeftReflectLE M] [ExistsAddOfLE M]

theorem sum_tsub_distrib (s : Finset ι) {f g : ι → M} (hfg : ∀ x ∈ s, g x ≤ f x) :
    ∑ x ∈ s, (f x - g x) = ∑ x ∈ s, f x - ∑ x ∈ s, g x := Multiset.sum_map_tsub _ hfg

