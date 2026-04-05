import Mathlib

variable {α : Type*}

variable [AddCommMonoid α] [PartialOrder α] [CanonicallyOrderedAdd α]
  [Sub α] [OrderedSub α] {a b c : α}

theorem tsub_le_tsub_iff_left (ha : AddLECancellable a) (hc : AddLECancellable c)
    (h : c ≤ a) : a - b ≤ a - c ↔ c ≤ b := by
  refine ⟨?_, fun h => tsub_le_tsub_left h a⟩
  rw [tsub_le_iff_left, ← hc.add_tsub_assoc_of_le h, hc.le_tsub_iff_right (h.trans le_add_self),
    add_comm b]
  apply ha

