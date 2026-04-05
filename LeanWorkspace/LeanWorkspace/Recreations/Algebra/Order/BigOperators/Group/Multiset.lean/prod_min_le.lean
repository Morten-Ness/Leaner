import Mathlib

variable {ι α β : Type*}

theorem prod_min_le [CommMonoid α] [LinearOrder α] [IsOrderedMonoid α]
    {s : Multiset ι} {f g : ι → α} :
    (s.map fun i ↦ min (f i) (g i)).prod ≤ min (s.map f).prod (s.map g).prod := by
  obtain ⟨l⟩ := s
  simp_rw [Multiset.quot_mk_to_coe'', Multiset.map_coe, Multiset.prod_coe]
  apply List.prod_min_le

