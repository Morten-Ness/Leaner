import Mathlib

variable {ι α β : Type*}

variable [AddCommMonoid α] [PartialOrder α]
  [AddCommMonoid β] [PartialOrder β] [SMulZeroClass α β]

variable [CeilDiv α β] {f : ι →₀ β} {a : α}

theorem ceilDiv_def (f : ι →₀ β) (a : α) : f ⌈/⌉ a = f.mapRange (· ⌈/⌉ a) (zero_ceilDiv _) := rfl

