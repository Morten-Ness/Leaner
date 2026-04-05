import Mathlib

variable {ι α β : Type*}

theorem max_prod_le [CommMonoid α] [LinearOrder α] [IsOrderedMonoid α]
    {s : Multiset ι} {f g : ι → α} :
    max (s.map f).prod (s.map g).prod ≤ (s.map fun i ↦ max (f i) (g i)).prod := by
  obtain ⟨l⟩ := s
  simp_rw [Multiset.quot_mk_to_coe'', Multiset.map_coe, Multiset.prod_coe]
  apply List.max_prod_le

