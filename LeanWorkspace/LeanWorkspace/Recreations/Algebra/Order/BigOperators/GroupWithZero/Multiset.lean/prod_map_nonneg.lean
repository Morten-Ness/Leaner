import Mathlib

variable {R : Type*} [CommMonoidWithZero R] [PartialOrder R] [ZeroLEOneClass R] [PosMulMono R]

variable {α : Type*}

theorem prod_map_nonneg {s : Multiset α} {f : α → R} (h : ∀ a ∈ s, 0 ≤ f a) :
    0 ≤ (s.map f).prod := by
  refine Multiset.prod_nonneg fun r hr ↦ ?_
  obtain ⟨a, ha, rfl⟩ := mem_map.mp hr
  exact h a ha

