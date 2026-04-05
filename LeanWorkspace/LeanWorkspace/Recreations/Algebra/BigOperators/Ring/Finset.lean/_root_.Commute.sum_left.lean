import Mathlib

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable [NonUnitalNonAssocSemiring R]

theorem _root_.Commute.sum_left (s : Finset ι) (f : ι → R) (b : R)
    (h : ∀ i ∈ s, Commute (f i) b) : Commute (∑ i ∈ s, f i) b := ((Commute.sum_right _ _ _) fun _i hi => (h _ hi).symm).symm

