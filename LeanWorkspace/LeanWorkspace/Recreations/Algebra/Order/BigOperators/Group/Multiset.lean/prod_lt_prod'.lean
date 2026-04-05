import Mathlib

variable {ι α β : Type*}

variable [CommMonoid α] [Preorder α] [IsOrderedCancelMonoid α] [MulLeftStrictMono α]
  {s : Multiset ι} {f g : ι → α}

theorem prod_lt_prod' (hle : ∀ i ∈ s, f i ≤ g i) (hlt : ∃ i ∈ s, f i < g i) :
    (s.map f).prod < (s.map g).prod := by
  obtain ⟨l⟩ := s
  simp only [Multiset.quot_mk_to_coe'', Multiset.map_coe, Multiset.prod_coe]
  exact List.prod_lt_prod' f g hle hlt

