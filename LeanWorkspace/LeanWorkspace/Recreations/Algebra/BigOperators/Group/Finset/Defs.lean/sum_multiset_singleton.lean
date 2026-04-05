import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

theorem sum_multiset_singleton (s : Finset ι) : ∑ a ∈ s, {a} = s.val := by
  simp only [sum_eq_multiset_sum, Multiset.sum_map_singleton]

