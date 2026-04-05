import Mathlib

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable [NonUnitalNonAssocSemiring R]

theorem _root_.Commute.sum_right (s : Finset ι) (f : ι → R) (b : R)
    (h : ∀ i ∈ s, Commute b (f i)) : Commute b (∑ i ∈ s, f i) := (Commute.multiset_sum_right _ _) fun b hb => by
    obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hb
    exact h _ hi

