import Mathlib

variable {α : Type*}

variable [AddCommMonoid α] [PartialOrder α] [CanonicallyOrderedAdd α]
  [Sub α] [OrderedSub α] {a b c : α}

theorem tsub_right_inj (ha : AddLECancellable a) (hb : AddLECancellable b)
    (hc : AddLECancellable c) (hba : b ≤ a) (hca : c ≤ a) : a - b = a - c ↔ b = c := by
  simp_rw [le_antisymm_iff, AddLECancellable.tsub_le_tsub_iff_left ha hb hba, AddLECancellable.tsub_le_tsub_iff_left ha hc hca,
    and_comm]

