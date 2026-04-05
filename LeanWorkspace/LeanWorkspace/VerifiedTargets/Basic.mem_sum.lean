import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

theorem mem_sum {a : M} {s : Finset ι} {m : ι → Multiset M} :
    a ∈ ∑ i ∈ s, m i ↔ ∃ i ∈ s, a ∈ m i := by
  induction s using Finset.cons_induction with grind

