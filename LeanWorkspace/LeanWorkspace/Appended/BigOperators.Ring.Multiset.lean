import Mathlib

section

variable {ι M M₀ R : Type*}

variable [NonUnitalNonAssocSemiring R] (s : Multiset R)

theorem multiset_sum_left (b : R) (h : ∀ a ∈ s, Commute a b) : Commute s.sum b := ((Commute.multiset_sum_right _ _) fun _ ha => (h _ ha).symm).symm

end

section

variable {ι M M₀ R : Type*}

variable [CommMonoidWithZero M₀] {s : Multiset M₀}

theorem prod_eq_zero (h : (0 : M₀) ∈ s) : s.prod = 0 := by
  rcases Multiset.exists_cons_of_mem h with ⟨s', hs'⟩; simp [hs', Multiset.prod_cons]

end
