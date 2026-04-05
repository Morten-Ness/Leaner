import Mathlib

variable {ι M M₀ R : Type*}

variable [NonUnitalNonAssocSemiring R] (s : Multiset R)

theorem multiset_sum_left (b : R) (h : ∀ a ∈ s, Commute a b) : Commute s.sum b := ((Commute.multiset_sum_right _ _) fun _ ha => (h _ ha).symm).symm

