import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

theorem disjoint_finset_sum_right {i : Finset ι} {f : ι → Multiset α}
    {a : Multiset α} : Disjoint a (i.sum f) ↔ ∀ b ∈ i, Disjoint a (f b) := by
  simpa only [disjoint_comm] using Multiset.disjoint_finset_sum_left

