import Mathlib

variable {α : Type*}

variable [AddCommMonoid α] [LinearOrder α] [CanonicallyOrderedAdd α] [Sub α] [OrderedSub α]
  {a b c : α}

theorem Even.tsub [AddLeftReflectLE α] {m n : α} (hm : Even m) (hn : Even n) :
    Even (m - n) := by
  obtain ⟨a, rfl⟩ := hm
  obtain ⟨b, rfl⟩ := hn
  refine ⟨a - b, ?_⟩
  obtain h | h := le_total a b
  · rw [tsub_eq_zero_of_le h, tsub_eq_zero_of_le (add_le_add h h), add_zero]
  · exact (tsub_add_tsub_comm h h).symm

