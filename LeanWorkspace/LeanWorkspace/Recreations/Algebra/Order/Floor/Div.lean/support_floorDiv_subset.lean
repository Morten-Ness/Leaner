import Mathlib

variable {ι α β : Type*}

variable [AddCommMonoid α] [PartialOrder α]
  [AddCommMonoid β] [PartialOrder β] [SMulZeroClass α β]

variable [FloorDiv α β] {f : ι →₀ β} {a : α}

theorem support_floorDiv_subset : (f ⌊/⌋ a).support ⊆ f.support := by
  simp +contextual [Finset.subset_iff, not_imp_not]

