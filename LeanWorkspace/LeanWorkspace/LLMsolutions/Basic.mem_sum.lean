import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

theorem mem_sum {a : M} {s : Finset ι} {m : ι → Multiset M} :
    a ∈ ∑ i ∈ s, m i ↔ ∃ i ∈ s, a ∈ m i := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro b s hb ih
    simp [hb, ih, or_left_comm, or_assoc]
