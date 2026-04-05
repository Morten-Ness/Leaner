import Mathlib

variable {ι α β : Type*}

variable [CommMonoid α] [Preorder α] [IsOrderedCancelMonoid α] [MulLeftStrictMono α]
  {s : Multiset ι} {f g : ι → α}

theorem prod_lt_prod_of_nonempty' (hs : s ≠ ∅) (hfg : ∀ i ∈ s, f i < g i) :
    (s.map f).prod < (s.map g).prod := by
  obtain ⟨i, hi⟩ := exists_mem_of_ne_zero hs
  exact Multiset.prod_lt_prod' (fun i hi => le_of_lt (hfg i hi)) ⟨i, hi, hfg i hi⟩

