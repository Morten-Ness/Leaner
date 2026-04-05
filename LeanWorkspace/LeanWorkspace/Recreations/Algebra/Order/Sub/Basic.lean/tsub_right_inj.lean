import Mathlib

variable {α : Type*}

variable [AddCommMonoid α] [PartialOrder α] [CanonicallyOrderedAdd α]
  [Sub α] [OrderedSub α] {a b c : α}

variable [AddLeftReflectLE α]

theorem tsub_right_inj (hba : b ≤ a) (hca : c ≤ a) : a - b = a - c ↔ b = c := Contravariant.AddLECancellable.tsub_right_inj Contravariant.AddLECancellable
    Contravariant.AddLECancellable hba hca

