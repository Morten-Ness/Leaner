import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

theorem disjoint_finset_sum_left {i : Finset ι} {f : ι → Multiset α} {a : Multiset α} :
    Disjoint (i.sum f) a ↔ ∀ b ∈ i, Disjoint (f b) a := by
  convert @Multiset.disjoint_sum_left _ a (map f i.val)
  simp

