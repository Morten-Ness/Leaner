import Mathlib

variable {R : Type*}

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]

variable {β : Type*} [Ring β] [PartialOrder β] [IsOrderedRing β]

theorem mem_iff_one_sub_mem {t : β} : t ∈ Set.Ioo (0 : β) 1 ↔ 1 - t ∈ Set.Ioo (0 : β) 1 := ⟨Set.Ioo.one_sub_mem, fun h => sub_sub_cancel 1 t ▸ Set.Ioo.one_sub_mem h⟩

