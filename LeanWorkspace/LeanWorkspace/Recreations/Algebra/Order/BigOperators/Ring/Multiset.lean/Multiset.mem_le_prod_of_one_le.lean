import Mathlib

variable {α β : Type*} [CommMonoid α] [CommMonoidWithZero β] [PartialOrder β] [PosMulMono β]

omit [CommMonoid α] in
theorem Multiset.mem_le_prod_of_one_le [ZeroLEOneClass β] {f : α → β} (h1 : ∀ a : α, 1 ≤ f a)
    {s : Multiset α} {a : α} (ha : a ∈ s) : f a ≤ (s.map f).prod := by
  obtain ⟨s', rfl⟩ := exists_cons_of_mem ha
  rw [map_cons, prod_cons]
  calc f a = f a * 1 := (mul_one (f a)).symm
    _ ≤ f a * (s'.map f).prod := by
      gcongr
      · exact le_trans (zero_le_one' β) (h1 a)
      · simp_all [one_le_prod]

