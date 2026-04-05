import Mathlib

variable {α : Type*}

variable [AddCommMonoid α] [PartialOrder α] [CanonicallyOrderedAdd α]
  [Sub α] [OrderedSub α] {a b c : α}

theorem add_tsub_cancel_iff_le : a + (b - a) = b ↔ a ≤ b := ⟨fun h => le_iff_exists_add.mpr ⟨b - a, h.symm⟩, add_tsub_cancel_of_le⟩

