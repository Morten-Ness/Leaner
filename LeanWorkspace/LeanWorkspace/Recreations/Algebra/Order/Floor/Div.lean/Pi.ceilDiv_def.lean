import Mathlib

variable {ι α β : Type*}

variable {π : ι → Type*} [AddCommMonoid α] [PartialOrder α]
  [∀ i, AddCommMonoid (π i)] [∀ i, PartialOrder (π i)]
  [∀ i, SMulZeroClass α (π i)]

variable [∀ i, CeilDiv α (π i)]

theorem ceilDiv_def (f : ∀ i, π i) (a : α) : f ⌈/⌉ a = fun i ↦ f i ⌈/⌉ a := rfl

