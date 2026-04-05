import Mathlib

variable {R : Type*}

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]

variable {β : Type*} [Ring β] [PartialOrder β] [IsOrderedRing β]

theorem one_sub_mem {t : β} (ht : t ∈ Set.Ioo (0 : β) 1) : 1 - t ∈ Set.Ioo (0 : β) 1 := by
  simp_all only [mem_Ioo, sub_pos, sub_lt_self_iff, and_self]

