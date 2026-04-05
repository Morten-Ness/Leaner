import Mathlib

variable {R : Type*} [CommMonoidWithZero R] [PartialOrder R] [ZeroLEOneClass R] [PosMulMono R]

variable {α : Type*}

theorem one_le_prod_map {s : Multiset α} {f : α → R} (h : ∀ a ∈ s, 1 ≤ f a) :
    1 ≤ (s.map f).prod := by
  refine Multiset.one_le_prod fun r hr ↦ ?_
  obtain ⟨a, ha, rfl⟩ := mem_map.mp hr
  exact h a ha

omit [PosMulMono R]

