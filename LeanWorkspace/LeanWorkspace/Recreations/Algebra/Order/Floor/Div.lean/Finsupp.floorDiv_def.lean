import Mathlib

variable {ι α β : Type*}

variable [AddCommMonoid α] [PartialOrder α]
  [AddCommMonoid β] [PartialOrder β] [SMulZeroClass α β]

variable [FloorDiv α β] {f : ι →₀ β} {a : α}

theorem floorDiv_def (f : ι →₀ β) (a : α) : f ⌊/⌋ a = f.mapRange (· ⌊/⌋ a) (zero_floorDiv _) := rfl

